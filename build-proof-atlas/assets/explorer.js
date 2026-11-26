"use strict";
const data = JSON.parse(document.querySelector("#atlas-data").textContent);
const claims = new Map(data.claims.map(c => [c.id,c]));
const views = {english:"Plain English", paper:"Paper", lamport:"Lamport proof", lean:"Lean"};
const basisLabels = {
  paper: "Follows paper proof",
  lean: "Lean-only proof route",
  aligned: "Aligned paper & Lean proof",
  supplied: "Proof supplied outside manuscript",
};
const pane = document.querySelector("#content");
function el(tag, text, cls) {
  const node = document.createElement(tag);
  if (text) node.textContent = text;
  if (cls) node.className = cls;
  return node;
}
function link(text, href, cls) {
  const a = el("a",text,cls); a.href = href; return a;
}
function route(id,view="english",graph=false) {
  return location.pathname+"#/"+(graph?"graph/":"claim/")+encodeURIComponent(id)+(graph?"":"?view="+view);
}
function locationState() {
  const [path,query] = location.hash.slice(1).split("?");
  let id; try {id = decodeURIComponent(path.replace(/^\/(graph|claim)\//,""));} catch { id=""; }
  const view = new URLSearchParams(query).get("view");
  return {id:id || data.focus || data.claims[0]?.id, view:Object.hasOwn(views,view)?view:"english", graph:path.startsWith("/graph/")};
}
function rich(text,tag="p") {
  const p=el(tag);
  for (const part of (text || "").split(/(\$[^$\n]+\$)/g)) {
    if (part.startsWith("$") && part.endsWith("$") && window.katex) {
      const span=el("span"); katex.render(part.slice(1,-1),span,{throwOnError:false,output:"htmlAndMathml",trust:false,macros:data.macros||{}}); p.append(span);
    } else p.append(document.createTextNode(part));
  }
  return p;
}
function tierLabel(tier) {
  return tier==="headline" ? "Headline result" : tier==="conjecture" ? "Conjecture" : "Supporting result";
}
function fillList(selected) {
  const list=document.querySelector("#claim-list"), term=document.querySelector("#search").value.toLowerCase().trim();
  list.replaceChildren();
  if (data.summary) {
    const h=data.summary.headline, s=data.summary.supporting, conj=data.summary.conjectures;
    const bits=[`Headline: ${h.unconditionally_closed}/${h.total} closed`];
    if (h.conditional) bits[0]+=` · ${h.conditional} cond.`;
    if (s.total) {
      let sp=`Supporting: ${s.unconditionally_closed}/${s.total} closed`;
      if (s.conditional) sp+=` · ${s.conditional} cond.`;
      bits.push(sp);
    }
    if (conj.total) bits.push(`Conjectures: ${conj.total}`);
    list.append(el("div", bits.join(" | "), "sidebar-summary"));
  }
  for (const c of claims.values()) {
    const tLabel = tierLabel(c.tier);
    if (!(c.reference+" "+c.title+" "+c.id+" "+(c.tier||"")+" "+tLabel).toLowerCase().includes(term)) continue;
    const a=link("",route(c.id),"claim-choice");
    a.append(el("small",c.reference+" · "+tLabel),el("span",c.title));
    if(c.verification.evidence) {
      a.append(el("small","✓ "+(c.verification.remote || "Machine verified on GitHub"),"verified-badge"));
      if(c.verification.supplied) a.append(el("small","Proof supplied outside manuscript"));
    } else a.append(el("small", [c.verification.label, c.verification.remote].filter(Boolean).join(" · ")));
    if(c.verification.step_verified && c.verification.step_badge) a.append(el("small","✓ "+c.verification.step_badge,"verified-badge"));
    if(c.verification.needs_author_confirmation || c.verification.needs_author_confirmation_via?.length) a.append(el("small","Needs author confirmation"));
    if(c.verification.approval) a.append(el("small",c.verification.approval,c.verification.approved?"approval approved":"approval"));
    if(c.id===selected) a.setAttribute("aria-current","page");
    list.append(a);
  }
  if (!list.querySelector(".claim-choice")) list.append(el("p","No matching claims."));
}
function relations(c, reverse=false) {
  return data.dependencies.filter(e=>reverse?e.prerequisite===c.id:e.claim===c.id);
}
function proofView(c,view) {
  pane.append(el("small",c.reference+" · "+tierLabel(c.tier)),el("h2",c.title));
  const v=c.verification;
  if(v.review_url) pane.append(link("Review this claim",v.review_url,"graph-link"));
  for(const [key,title] of [["stronger_result","Lean proves more"],["author_scope","Author’s scope note"]]){
    if(v[key]){
      const note=el("aside",null,"scope-note");
      note.append(el("strong",title),el("p",v[key]));
      pane.append(note);
    }
  }
  if(c.basis==="supplied"){
    const note=el("aside",null,"scope-note");
    const p=el("p","This claim is stated in the manuscript without a complete proof (for example, an unproved remark or skipped step). Lean supplies the checked argument outside the PDF. ");
    p.append(link("Open supplement.md", v.supplement_url || "supplement.md"));
    note.append(el("strong","Proof supplied outside manuscript"), p);
    pane.append(note);
  }
  if(v.needs_author_confirmation){
    const note=el("aside",null,"scope-note");
    note.append(el("strong","Needs author confirmation"),
      el("p","This claim uses an unattended reading (chosen reading, added hypothesis, or restriction) recorded during a quick triage pass. Review the comparison to confirm or adjust it."));
    pane.append(note);
  }
  if(v.needs_author_confirmation_via?.length){
    const note=el("aside",null,"scope-note");
    const p=el("p","Depends on unconfirmed unattended reading(s) in: ");
    v.needs_author_confirmation_via.forEach((item,idx)=>{
      if(idx) p.append(document.createTextNode(", "));
      p.append(item.id && claims.has(item.id) ? link(item.reference, route(item.id)) : document.createTextNode(item.reference));
    });
    note.append(el("strong","Needs author confirmation (upstream dependency)"), p);
    pane.append(note);
  }
  if(v.approval){
    // Two separate claims: Lean proved the formal statement; the author approved it as the paper's.
    const marks=el("div",null,"lean-checks");
    marks.append(el("span","✓ "+v.label,"status"),link(v.approval,v.review_url,"approval approved"));
    pane.append(marks);
  }
  if(v.step_verified && v.step_badge){
    const stepBar=el("div",null,"lean-checks");
    stepBar.append(link("✓ "+v.step_badge,route(c.id,"lamport"),"verified-badge"));
    if(v.supplied_step_count > 0 && v.supplement_url) stepBar.append(link("Supplied steps in supplement.md",v.supplement_url));
    pane.append(stepBar);
  }
  if(v.evidence){
    const proof=el("div",null,"lean-checks");
    proof.append(link("✓ "+v.remote,v.url,"verified-badge"));
    if(v.paranoid && v.kernels_checked?.length) proof.append(el("span","Kernels: "+v.kernels_checked.join(", "),"muted"));
    proof.append(link("Verification record · "+v.commit.slice(0,7),v.evidence));
    if(v.artifact){
      const download=link("GitHub artifact (sign-in required)",v.artifact);
      download.dataset.artifactRecord=v.evidence;
      proof.append(download);
    }
    pane.append(proof);
  }
  pane.append(link("Show in dependency graph",route(c.id,"english",true),"graph-link"));
  const tabs=el("nav",null,"views");tabs.setAttribute("aria-label","Reading view");
  for(const [id,label] of Object.entries(views)){
    const a=link(label,route(c.id,id)); if(id===view) a.setAttribute("aria-current","page"); tabs.append(a);
  }
  pane.append(tabs);
  // Only the Lean view is tied to the checked proof; the readable views are written separately.
  if(view==="english") pane.append(el("p","Explanation, not machine-checked. The Lean view shows what Lean checked.","unchecked-note"));
  else if(view==="lamport"){
    if(c.step_verification?.verified){
      pane.append(el("p","1:1 step dependency graph and Lean lemma bindings are kernel-checked ("+c.step_verification.badge+"); step prose remains an explanation.","unchecked-note"));
    } else {
      pane.append(el("p","Explanation, not machine-checked. The Lean view shows what Lean checked.","unchecked-note"));
    }
  }
  if(view==="english") {
    pane.append(el("h3","What the claim says"),rich(c.summary || "An English summary is pending. The manuscript view contains the source statement."));
    pane.append(el("h3",c.kind==="conjecture"?"Open question":"High-level proof sketch"),rich(c.sketch || (c.kind==="conjecture"?"The manuscript presents this as a conjecture.":"A proof sketch has yet to be recorded.")));
  } else if(view==="paper"){
    const url="manuscript.pdf"+(c.page?"#page="+c.page:"");
    pane.append(link(c.page?"Open PDF at page "+c.page:"Open manuscript PDF",url));
    if(c.page){const frame=el("iframe");frame.title="Paper passage, page "+c.page;frame.src=url;pane.append(frame);}
    const details=el("details");details.open=!c.page;
    details.append(el("summary","Verbatim TeX · "+c.file+", line "+c.line),el("pre",c.excerpt));pane.append(details);
    if(c.differences!==undefined){
      // From the comparison the author reviews: each case that does not simply agree with the paper.
      pane.append(el("h3","Differences from the paper"));
      if(c.differences===null) pane.append(el("p","Differences not classified.","muted"));
      else if(!c.differences.length) pane.append(el("p","Every compared case agrees.","muted"));
      for(const d of c.differences||[]){
        const item=el("div",null,"proof-step");
        item.append(el("strong",d.kind+" · "+d.case),rich("Paper: "+d.paper),rich("Lean: "+d.lean),rich(d.why));
        pane.append(item);
      }
    }
  } else if(view==="lamport"){
    if(c.basis){
      const bLine=el("p","Proof basis: "+(basisLabels[c.basis]||c.basis)+(c.basis==="supplied"?" · ":""),"muted");
      if(c.basis==="supplied") bLine.append(link("Read in supplement.md", v.supplement_url || "supplement.md"));
      pane.append(bLine);
    }
    if(c.step_verification?.steps?.length){
      const sv=c.step_verification;
      const statusLine=el("p",null,"muted");
      if(sv.verified && sv.badge){
        statusLine.append(el("span","✓ "+sv.badge,"verified-badge"),
          document.createTextNode(" · "+sv.paper_steps+" verbatim paper / "+sv.supplied_steps+" supplied step(s)"));
      } else {
        statusLine.append(document.createTextNode("Draft 1:1 step map (awaiting Lean --step-map audit) · "+sv.paper_steps+" verbatim paper / "+sv.supplied_steps+" supplied step(s)"));
      }
      if(sv.supplied_steps > 0 && v.supplement_url){
        statusLine.append(document.createTextNode(" · "), link("Open supplement.md", v.supplement_url));
      }
      pane.append(el("h3","Structured Lamport steps"), statusLine);
      for(const s of sv.steps){
        const box=el("div",null,"proof-step");
        const heading=s.id+(s.title?" · "+s.title:"");
        box.append(el("strong",heading));
        const prov=el("p",null,"muted");
        if(s.origin==="paper"){
          const loc=s.tex_file?(s.tex_file+(s.tex_line?" L"+s.tex_line:"")):"";
          prov.append(document.createTextNode("Origin: Paper (verbatim TeX verified"+(loc?", "+loc:"")+")"));
        } else {
          prov.append(document.createTextNode("Origin: Supplied outside manuscript"));
          if(v.supplement_url) prov.append(document.createTextNode(" · "), link("supplement.md", v.supplement_url));
        }
        prov.append(document.createTextNode(" · Lean lemma: "), el("code",s.lemma));
        if(s.file && s.lines) prov.append(document.createTextNode(" ("+s.file+" L"+s.lines[0]+")"));
        const deps=(s.used_deps || s.step_deps || []);
        prov.append(document.createTextNode(" · step_deps: "+(deps.length?deps.join(", "):"none")));
        box.append(prov);
        if(s.text) box.append(rich(s.text));
        if(s.tex){
          const d=el("details");
          d.append(el("summary","Verbatim TeX excerpt"), el("pre",s.tex));
          box.append(d);
        }
        pane.append(box);
      }
    }
    if(c.steps){
      pane.append(el("p",c.origin || "Structured proof","muted"));
      if(c.source_url && /^https?:\/\//.test(c.source_url)) pane.append(link("Source companion and mapping ledger",c.source_url));
      for(const line of c.steps.split(/\n\s*\n/)){
        const match=line.match(/^\*\*(.*?)\*\*\s*([\s\S]*)$/);
        if(match){const step=el("div",null,"proof-step");step.append(rich(match[1],"strong"),rich(match[2]));pane.append(step);}
        else pane.append(rich(line));
      }
    }
    if(c.structured){const note=el("details");note.open=!c.steps && !c.step_verification?.steps?.length;note.append(el("summary","Pilot supplement"),el("pre",c.structured));pane.append(note);}
    if(!c.steps && !c.structured && !c.step_verification?.steps?.length) pane.append(el("p",c.kind==="conjecture"?"This conjecture has no recorded proof.":"No structured argument has been imported yet."));
  } else {
    const checks=el("div",null,"lean-checks");
    checks.append(el("strong",c.verification.label));
    if(v.step_verified && v.step_badge) checks.append(el("span","✓ "+v.step_badge,"verified-badge"));
    if(c.axiom_profile) checks.append(el("span",c.axiom_profile,"muted"));
    if(v.approval) checks.append(el("strong",v.approval));
    if(c.audit_log) checks.append(link("Declaration and axiom audit",c.audit_log));
    if(c.log) checks.append(link("Lean run log",c.log));
    if(v.remote && !v.evidence) checks.append(link(v.remote,v.url));
    pane.append(checks);
    if(v.conditional && v.assumes?.length){
      pane.append(el("h3","Assumed prerequisites (conditional proof)"),
        el("p","Lean checked this claim assuming the following unproved statement(s). Closing those prerequisites and reassembling upgrades this claim to Lean checked.","muted"));
      const list=el("ul");
      for(const dep of v.assumes){
        const item=el("li");
        if(dep.id && claims.has(dep.id)) item.append(link(dep.reference, route(dep.id)), document.createTextNode(" · "), el("code",dep.expected));
        else item.append(el("code",dep.expected));
        list.append(item);
      }
      pane.append(list);
    }
    if(c.noncomputable_constants?.length){
      const nc=el("p","Noncomputable definitions in statement: ","muted");
      c.noncomputable_constants.forEach((name,idx)=>{
        if(idx) nc.append(document.createTextNode(", "));
        nc.append(el("code",name));
      });
      nc.append(document.createTextNode(". Check whether any paper claim of an explicit or computable algorithm is affected."));
      pane.append(nc);
    }
    const thirdParty=(c.external_packages||[]).filter(p=>p.third_party);
    if(thirdParty.length){
      pane.append(el("h3","Third-party external dependencies"),el("p","This Lean package imports non-Mathlib external repositories.","muted"));
      const list=el("ul");
      for(const pkg of thirdParty){
        const item=el("li");
        item.append(el("code",pkg.name),document.createTextNode(" ("+(pkg.rev||"").slice(0,12)+")"+(pkg.url?" · "+pkg.url:"")));
        list.append(item);
      }
      pane.append(list);
    }
    if(c.unfolded_signatures?.length){
      const details=el("details");
      details.append(el("summary","Notation-free Lean signatures (pp.notation false)"));
      for(const sig of c.unfolded_signatures){
        const heading=sig.name+" · "+sig.file+(sig.lines?" L"+sig.lines[0]:"")+(sig.noncomputable?" · noncomputable":"");
        details.append(el("h4",heading),el("pre",sig.pp_no_notation));
      }
      pane.append(details);
    }
    if(c.hypotheses){
      // The audit derived this proposition from the statement and checked the example proves it.
      const note=el("p","The hypotheses can hold. ","muted");
      note.append(el("code",c.hypotheses.declaration),document.createTextNode(" proves:"));
      pane.append(note,el("pre",c.hypotheses.proposition));
    } else if(c.audit_log) pane.append(el("p","No checked example shows the hypotheses can hold.","muted"));
    if(c.undistilled){
      pane.append(el("p","Exploratory proof (undistilled). Factor reusable glue into Routine/ and mark distilled once refined.","muted"));
    } else if(c.distilled===true){
      pane.append(el("p","Distilled proof (factored into Routine/ with clean paper-statement target).","muted"));
    }
    if(c.basis){
      const bNote=el("p","Proof basis: "+(basisLabels[c.basis]||c.basis)+(c.basis==="supplied"?" · ":""),"muted");
      if(c.basis==="supplied") bNote.append(link("Open supplement.md", v.supplement_url || "supplement.md"));
      pane.append(bNote);
    }
    if(c.proof_metrics){
      const m=c.proof_metrics, bits=[];
      if(m.checked_lean_loc!==undefined) bits.push(m.checked_lean_loc+" checked Lean LoC");
      if(m.reachable_local_defs!==undefined) bits.push(m.reachable_local_defs+" reachable local defs");
      if(m.reachable_local_theorems!==undefined) bits.push(m.reachable_local_theorems+" reachable local theorems");
      if(bits.length) pane.append(el("p","Proof size: "+bits.join(" · "),"muted"));
    }
    if(c.step_verification?.verified){
      const sv=c.step_verification;
      pane.append(el("h3","1:1 Step-Lemma Expr Audit"));
      const summaryLine=el("p",sv.badge+" · "+sv.step_count+" step(s) ("+sv.paper_steps+" paper, "+sv.supplied_steps+" supplied) · main: ","muted");
      summaryLine.append(el("code",sv.main_declaration || ""));
      if(sv.main_steps?.length) summaryLine.append(document.createTextNode(" (uses "+sv.main_steps.join(", ")+")"));
      if(sv.step_map_sha256) summaryLine.append(document.createTextNode(" · sha256: "), el("code",sv.step_map_sha256.slice(0,12)));
      pane.append(summaryLine);
      const list=el("ul");
      for(const s of sv.steps){
        const item=el("li");
        item.append(el("strong",s.id), document.createTextNode(" ["+s.origin+"] · "), el("code",s.lemma));
        if(s.file && s.lines) item.append(document.createTextNode(" ("+s.file+" L"+s.lines[0]+")"));
        const deps=s.used_deps || s.step_deps || [];
        item.append(document.createTextNode(" · step_deps: "+(deps.length?deps.join(", "):"none")));
        if(s.used_statements?.length) item.append(document.createTextNode(" · statements: "), el("code",s.used_statements.join(", ")));
        list.append(item);
      }
      pane.append(list);
    }
    if(c.lean_dependencies){
      const ld=c.lean_dependencies;
      const groups=[
        ["Used in both paper & Lean proof", ld.both||[]],
        ["Paper-only dependency (Lean proved independently)", ld.paper_only||[]],
        ["Lean-only prerequisite", ld.lean_only||[]],
      ].filter(([,items])=>items.length);
      if(groups.length || (ld.used_local_theorems||[]).length || (ld.used_local_statements||[]).length){
        pane.append(el("h3","Kernel-extracted Lean dependencies"));
        for(const [heading, items] of groups){
          const p=el("p",heading+": ","muted");
          items.forEach((dep,idx)=>{
            if(idx) p.append(document.createTextNode(", "));
            p.append(dep.id && claims.has(dep.id) ? link(dep.reference, route(dep.id)) : document.createTextNode(dep.reference));
            if(dep.lean_refs?.length) p.append(document.createTextNode(" ("), el("code", dep.lean_refs.join(", ")), document.createTextNode(")"));
          });
          pane.append(p);
        }
        if((ld.used_local_theorems||[]).length || (ld.used_local_statements||[]).length){
          const details=el("details");
          details.append(el("summary","Reachable local Lean theorems & .Statement constants"));
          if(ld.used_local_theorems?.length){
            details.append(el("p","Local theorems ("+ld.used_local_theorems.length+"): "+ld.used_local_theorems.join(", "),"muted"));
          }
          if(ld.used_local_statements?.length){
            details.append(el("p","Statement constants ("+ld.used_local_statements.length+"): "+ld.used_local_statements.join(", "),"muted"));
          }
          pane.append(details);
        }
      }
    }
    if(c.deferred_bridging_lemmas?.length){
      pane.append(el("h3","Deferred Mathlib bridging lemmas"));
      const bl=el("ul");
      for(const item of c.deferred_bridging_lemmas) bl.append(el("li",item));
      pane.append(bl);
    }
    pane.append(rich(c.scope || "No Lean formalization has been selected for this claim."));
    if(c.subproofs?.length){
      const list=el("ol");
      for(const part of c.subproofs){
        const item=el("li",part.title+" · "+part.status);
        if(part.declaration) item.append(document.createTextNode(" "),el("code",part.declaration));
        list.append(item);
      }
      pane.append(el("h3","Subproofs"),list);
    }
    if(c.defaults?.length){
      // Lean makes every function total; the comparison should account for each use.
      pane.append(el("h3","Lean default values in these definitions"),el("p","Lean gives these operations a value even where the mathematics leaves them undefined. The comparison should say, for each, why the default cannot arise under the hypotheses, or what it means if it does.","muted"));
      const list=el("ul");
      for(const d of c.defaults){
        const item=el("li");
        item.append(el("code",d.construct),document.createTextNode((d.type?" on "+d.type:"")+" in "),el("code",d.constant),
          document.createTextNode(" ("+d.file+(d.lines?" L"+d.lines[0]:"")+") · "+d.meaning));
        list.append(item);
      }
      pane.append(list);
    }
    for(const source of c.sources){pane.append(el("h3",source.path),el("pre",source.text));}
  }
}
function render(){
  const state=locationState();
  const home=document.body.dataset.entry==="home" && !location.hash.startsWith("#/");
  document.querySelector("#folio-home").hidden=!home;
  document.querySelector(".workspace").hidden=home;
  document.querySelector(".running").hidden=home;
  const current=home?"home":state.graph?"graph":"reader";
  for(const a of document.querySelectorAll("[data-nav]")){
    if(a.dataset.nav===current) a.setAttribute("aria-current","page");
    else a.removeAttribute("aria-current");
  }
  document.querySelector(".citation").open=false;
  if(graphState.resize){graphState.resize.disconnect();graphState.resize=null;}
  const hadNodeFocus=document.activeElement?.closest(".graph-node");
  document.body.classList.toggle("graph-mode",state.graph);
  document.querySelector("#graph-nav").href=route(state.id || data.focus || "", "english",true);
  if(home){document.title=data.title+" | Proof Atlas";return;}
  if(claims.has(state.id)) document.querySelector('[data-nav="reader"]').href=route(state.id,state.view);
  fillList(state.id);pane.replaceChildren();
  const c=claims.get(state.id);
  if(!c){pane.append(el("h2",claims.size?"Claim not found":"No claims imported yet"));return;}
  if(state.graph) graphView(c); else proofView(c,state.view);
  if(state.graph && hadNodeFocus) pane.querySelector('.graph-node[aria-current="true"]')?.focus({preventScroll:true});
  document.title=(state.graph?"Dependency graph":c.reference+" · "+c.title)+" | Proof Atlas";
}
document.querySelector("#search").addEventListener("input",()=>fillList(locationState().id));
const summary=document.querySelector(".feature-summary");
if(summary) summary.replaceChildren(...rich(summary.textContent).childNodes);
window.addEventListener("hashchange",render);render();
