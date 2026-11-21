"""Offline integration regression. Set ELAN_TOOLCHAIN to an installed Lean pin."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import audit_lean


@unittest.skipUnless(os.environ.get("ELAN_TOOLCHAIN"), "requires an installed pinned Lean toolchain")
class AuditClosure(unittest.TestCase):
    def test_local_dependency_stability(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root/"lean-toolchain").write_text(pin)
            (root/"lakefile.toml").write_text('name = "Example"\n[[lean_lib]]\nname = "Pkg"\n')
            (root/"Pkg").mkdir()
            sources = {
                "Pkg/Base.lean": "def quantity := 2\n",
                "Pkg/Proof.lean": "import Pkg.Base\ntheorem quantity_eq : quantity = 2 := rfl\n",
                "Pkg/Expected.lean": "def Statement : Prop := 2 = (2 : Nat)\n",
                "Pkg/Unrelated.lean": "-- independent claim\n",
                "Contract.lean": "import Pkg.Proof\n/- import Pkg.Unrelated -/\nimport Pkg.Expected\n",
            }
            for name, body in sources.items():
                (root/name).write_text(body, encoding="utf-8")
            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)
            args = SimpleNamespace(package=root, contract="Contract.lean", expected="Statement",
                                   declaration="quantity_eq", target=["Pkg.Proof"])

            def run_with_edit(path):
                build = audit_lean.run
                def edit_after_build(*args, **kwargs):
                    build(*args, **kwargs)
                    with (root/path).open("a", encoding="utf-8") as source:
                        source.write("-- parallel edit\n")
                return patch.object(audit_lean, "run", edit_after_build)

            with run_with_edit("Pkg/Unrelated.lean"):
                receipt = audit_lean.audit(args)
            self.assertEqual(receipt["input_scope"], "module-closure")
            self.assertEqual(set(receipt["checked_inputs"]),
                             {"lean-toolchain", "lakefile.toml", "lake-manifest.json",
                              "Pkg/Base.lean", "Pkg/Proof.lean", "Pkg/Expected.lean", "Contract.lean"})
            with run_with_edit("Pkg/Base.lean"), self.assertRaisesRegex(ValueError, "changed during the audit"):
                audit_lean.audit(args)

            # A custom source directory requests the conservative package-wide receipt.
            with (root/"lakefile.toml").open("a", encoding="utf-8") as config:
                config.write('srcDir = "."\n')
            fallback = audit_lean.audit(args)
            self.assertEqual(fallback["input_scope"], "full-package")
            self.assertIn("Pkg/Unrelated.lean", fallback["checked_inputs"])

    def test_statements_stay_independent_of_proofs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root/"lean-toolchain").write_text(pin)
            (root/"lakefile.toml").write_text('name = "Example"\n[[lean_lib]]\nname = "Statements"\n'
                                              '[[lean_lib]]\nname = "Proofs"\n')
            (root/"Statements").mkdir()
            (root/"Proofs").mkdir()
            sources = {
                "Statements/Defs.lean": "def rate (n : Nat) : Nat := n + 1\n",
                "Statements/Main.lean": "import Statements.Defs\ndef Statement : Prop := ∀ n, rate n > n\n",
                "Proofs/Helper.lean": "import Statements.Defs\ndef helperRate (n : Nat) : Nat := n + 1\n"
                                      "def ProofStatement : Prop := ∀ n, helperRate n > n\n",
                "Proofs/Main.lean": "import Statements.Main\nimport Proofs.Helper\n"
                                    "theorem main : Statement := fun n => Nat.lt_succ_self n\n"
                                    "theorem main' : ProofStatement := fun n => Nat.lt_succ_self n\n",
                "Contract.lean": "import Statements.Main\nimport Proofs.Main\n"
                                 "def ContractStatement : Prop := ∀ n, rate n > n\n",
            }
            for name, body in sources.items():
                (root/name).write_text(body, encoding="utf-8")
            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)

            def audit(expected="Statement", declaration="main", statements=("Statements",)):
                return audit_lean.audit(SimpleNamespace(package=root, contract="Contract.lean", expected=expected,
                                                        declaration=declaration, target=["Proofs.Main"],
                                                        statements=list(statements)))

            self.assertEqual(audit()["statements"], ["Statements"])
            # A proposition defined in a proof module or in the contract is rejected by name and file.
            with self.assertRaisesRegex(ValueError, r"ProofStatement is defined in Proofs\.Helper \(Proofs/Helper\.lean\)"):
                audit(expected="ProofStatement", declaration="main'")
            with self.assertRaisesRegex(ValueError, r"ContractStatement is defined in the contract Contract\.lean"):
                audit(expected="ContractStatement")
            # So is a statement module importing a proof module, directly or through another statement module.
            main = root/"Statements/Main.lean"
            main.write_text("import Statements.Defs\nimport Proofs.Helper\ndef Statement : Prop := ∀ n, helperRate n > n\n",
                            encoding="utf-8")
            with self.assertRaisesRegex(ValueError, r"Statements/Main\.lean imports Proofs\.Helper \(Proofs/Helper\.lean\)"):
                audit()
            main.write_text(sources["Statements/Main.lean"], encoding="utf-8")
            defs = root/"Statements/Defs.lean"
            defs.write_text("import Proofs.Helper\ndef rate (n : Nat) : Nat := helperRate n\n")
            (root/"Proofs/Helper.lean").write_text("def helperRate (n : Nat) : Nat := n + 1\n"
                                                   "def ProofStatement : Prop := ∀ n, helperRate n > n\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, r"Statements/Defs\.lean imports Proofs\.Helper"):
                audit()
            # Without a statement path the old layout still passes, with a warning.
            with tempfile.TemporaryFile("w+", encoding="utf-8") as err, patch.object(sys, "stderr", err):
                self.assertEqual(audit(statements=())["statements"], [])
                err.seek(0)
                self.assertIn("no --statements path was given", err.read())

    def test_statement_check_requires_verified_source_layout(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root/"lean-toolchain").write_text(pin)
            (root/"lakefile.toml").write_text(
                'name = "Example"\ndefaultTargets = ["Statements"]\n'
                '[[lean_lib]]\nname = "Statements"\n'
                '[[lean_lib]]\nname = "Proofs"\nsrcDir = "implementation"\n')
            (root/"Statements").mkdir()
            (root/"implementation/Proofs").mkdir(parents=True)
            (root/"implementation/Proofs/Helper.lean").write_text("def quantity := 2\n")
            (root/"Statements/Main.lean").write_text(
                "import Proofs.Helper\ndef Statement : Prop := quantity = 2\n")
            (root/"Statements.lean").write_text("import Statements.Main\n")
            (root/"Contract.lean").write_text("import Statements.Main\ntheorem claim : Statement := rfl\n")
            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)
            args = SimpleNamespace(package=root, contract="Contract.lean", expected="Statement",
                                   declaration="claim", target=["Statements.Main"], statements=[])
            receipt = audit_lean.audit(args)
            self.assertEqual(receipt["input_scope"], "full-package")
            self.assertIn("implementation/Proofs/Helper.lean", receipt["checked_inputs"])
            args.statements = ["Statements"]
            for targets in (["Statements.Main"], []):
                with self.subTest(targets=targets):
                    args.target = targets
                    with self.assertRaisesRegex(ValueError, "Cannot verify statement independence: Custom Lean library"):
                        audit_lean.audit(args)


    def test_default_value_uses_in_statement_definitions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root/"lean-toolchain").write_text(pin)
            (root/"lakefile.toml").write_text('name = "Example"\n[[lean_lib]]\nname = "Pkg"\n')
            (root/"Pkg").mkdir()
            sources = {
                "Pkg/Defs.lean": (
                    "instance : Inv Nat := ⟨fun n => n⟩\n"
                    "def gap (a b : Nat) : Nat := a - b\n"
                    "def share (a n : Nat) : Nat := a / n + a⁻¹\n"
                    "-- Proofs are not followed: this subtraction is not part of the statement.\n"
                    "theorem half_le (a : Nat) : a / 2 ≤ a := by\n  have := Nat.sub_le a 1; exact Nat.div_le_self a 2\n"
                    "def half (a : Nat) : {m : Nat // m ≤ a} := ⟨a / 2, half_le a⟩\n"
                    "def ratio (a b : Int) : Int := a / b - b\n"
                    "def Statement : Prop :=\n  ∀ a b, gap a b ≤ a ∧ (half a).1 ≤ share a 1 + a ∧ ratio a b = ratio a b\n"),
                "Pkg/Proof.lean": "import Pkg.Defs\ntheorem main : Statement := fun a b => ⟨Nat.sub_le a b, by\n"
                                  "  have := (half a).2; simp [share]; omega, rfl⟩\n",
                "Contract.lean": "import Pkg.Defs\nimport Pkg.Proof\n",
            }
            for name, body in sources.items():
                (root/name).write_text(body, encoding="utf-8")
            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)
            receipt = audit_lean.audit(SimpleNamespace(package=root, contract="Contract.lean", expected="Statement",
                                                       declaration="main", target=["Pkg.Proof"]))
            where = dict(file="Pkg/Defs.lean")
            self.assertEqual(receipt["defaults"], [
                dict(constant="gap", **where, lines=[2, 2], construct="HSub.hSub", type="Nat"),
                dict(constant="ratio", **where, lines=[8, 8], construct="HDiv.hDiv", type="Int"),
                dict(constant="share", **where, lines=[3, 3], construct="HDiv.hDiv", type="Nat"),
                dict(constant="share", **where, lines=[3, 3], construct="Inv.inv", type="Nat"),
            ])
            self.assertEqual(audit_lean.default_meaning(receipt["defaults"][0]), "a − b = 0 when b > a")
            self.assertNotIn("defaults", receipt["statement"])

    def test_statement_digest_follows_definitions_not_proofs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pin = os.environ["ELAN_TOOLCHAIN"]
            (root/"lean-toolchain").write_text(pin)
            (root/"lakefile.toml").write_text('name = "Example"\n[[lean_lib]]\nname = "Pkg"\n')
            (root/"Pkg").mkdir()
            defs = "def rate (n : Nat) : Nat := n + 1\ndef Statement : Prop := ∀ n, rate n > n\n"
            sources = {
                "Pkg/Defs.lean": defs,
                "Pkg/Proof.lean": "import Pkg.Defs\ntheorem main : Statement := by\n  intro n; unfold rate; exact Nat.lt_succ_self n\n",
                "Contract.lean": "import Pkg.Defs\nimport Pkg.Proof\n",
            }
            for name, body in sources.items():
                (root/name).write_text(body, encoding="utf-8")
            env = os.environ.copy()
            lake = audit_lean.select_lake(root, pin, env, sys.stderr, offline=True)
            subprocess.run([*lake, "update"], cwd=root, env=env, check=True)
            args = SimpleNamespace(package=root, contract="Contract.lean", expected="Statement",
                                   declaration="main", target=["Pkg.Proof"])

            def statement():
                return audit_lean.audit(args)["statement"]

            def edit(name, old, new):
                path = root/name
                path.write_text(path.read_text(encoding="utf-8").replace(old, new), encoding="utf-8")

            first = statement()
            self.assertEqual({c["name"]: c["file"] for c in first["constants"]},
                             {"Statement": "Pkg/Defs.lean", "rate": "Pkg/Defs.lean"})
            self.assertEqual(first["constants"][0]["lines"], [2, 2])
            # Proofs are outside the approved statement.
            edit("Pkg/Proof.lean", "exact Nat.lt_succ_self n", "omega")
            self.assertEqual(statement()["sha256"], first["sha256"])
            # Comments, layout and bound-variable names are outside it too.
            edit("Pkg/Defs.lean", "def rate (n : Nat) : Nat := n + 1", "-- the rate\ndef rate  (m : Nat) : Nat :=\n  m + 1")
            self.assertEqual(statement()["sha256"], first["sha256"])
            # A definition the statement unfolds to is inside it.
            edit("Pkg/Defs.lean", "m + 1", "m + 2")
            changed = statement()
            self.assertNotEqual(changed["sha256"], first["sha256"])
            before = {c["name"]: c["sha256"] for c in first["constants"]}
            self.assertEqual([c["name"] for c in changed["constants"] if c["sha256"] != before[c["name"]]], ["rate"])


if __name__ == "__main__":
    unittest.main()
