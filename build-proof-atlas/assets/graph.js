"use strict";
// Dagre handles branching, disconnected components and cyclic input. Positions are
// computed from the recorded relationships; paper-specific geometry is unnecessary.
const graphState = {chainOnly:false, camera:null, autoFit:true, layoutKey:"", resize:null};
const EDGE_GROUNDING_LABELS = {
  both: "Used in both paper & Lean proof",
  paper_only: "Paper-only dependency",
  lean_only: "Lean-only prerequisite",
  paper: "Paper dependency",
};

function graphSVG(tag, attrs={}) {
  const n=document.createElementNS("http://www.w3.org/2000/svg",tag);
  for(const [key,value] of Object.entries(attrs)) n.setAttribute(key,String(value));
  return n;
}
function reachable(id, adjacency) {
  const seen=new Set([id]), pending=[id];
  while(pending.length) {
    for(const next of adjacency.get(pending.pop()) || []) {
      if(!seen.has(next)) {seen.add(next);pending.push(next);}
    }
  }
  seen.delete(id);return seen;
}
function graphButton(label, action) {
  const b=el("button",label);b.type="button";b.onclick=action;return b;
}
function nodeTitle(text, limit) {
  const lines=[""];
  for(const word of text.split(/\s+/)){
    const i=lines.length-1, line=[lines[i],word].filter(Boolean).join(" ");
    if(line.length<=limit) lines[i]=line;
    else if(lines[i] && lines.length<3) lines.push(word);
    else {lines[i]=line.slice(0,limit-1).trimEnd()+"…";break;}
  }
  return lines;
}
function smoothEdge(points) {
  const first=points[0], last=points[points.length-1];
  let path="M "+first.x+" "+first.y;
  for(let i=1;i<points.length-1;i++){
    const a=points[i], b=points[i+1];
    path+=" Q "+a.x+" "+a.y+" "+(a.x+b.x)/2+" "+(a.y+b.y)/2;
  }
  return path+" L "+last.x+" "+last.y;
}

function graphView(selected) {
  const parents=new Map(), children=new Map();
  for(const id of claims.keys()){parents.set(id,[]);children.set(id,[]);}
  for(const e of data.dependencies){
    parents.get(e.claim).push(e.prerequisite);children.get(e.prerequisite).push(e.claim);
  }
  const up=reachable(selected.id,parents), down=reachable(selected.id,children);
  const trace=new Set([selected.id,...up,...down]);
  const shown=[...claims.values()].filter(c=>!graphState.chainOnly || trace.has(c.id));
  const ids=new Set(shown.map(c=>c.id));
  const edges=data.dependencies.filter(e=>ids.has(e.claim)&&ids.has(e.prerequisite));

  const head=el("div",null,"graph-head"), title=el("div");
  title.append(el("h2","Dependency graph"),el("p","Showing "+shown.length+" of "+claims.size+" paper claims  ·  "+edges.length+" recorded "+(edges.length===1?"dependency":"dependencies")));
  const picker=el("select");picker.setAttribute("aria-label","Select a claim in the graph");
  for(const c of claims.values()){const option=el("option",c.reference+" · "+c.title);option.value=c.id;picker.append(option);}
  picker.value=selected.id;picker.onchange=()=>{location.href=route(picker.value,"english",true);};
  head.append(title,picker);pane.append(head);
  const layout=el("div",null,"graph-layout"), main=el("div",null,"graph-main"), inspector=el("section",null,"graph-inspector");
  pane.append(layout);layout.append(main,inspector);
  const board=el("div",null,"graph-board"), tools=el("div",null,"graph-tools");
  main.append(board);board.append(tools);
  const modes=el("div",null,"graph-modes");
  for(const [only,label] of [[false,"Whole paper"],[true,"Selected chain"]]){
    const b=graphButton(label,()=>{graphState.chainOnly=only;graphState.camera=null;render();document.querySelector('.graph-modes [aria-pressed="true"]').focus();});
    b.setAttribute("aria-pressed",String(graphState.chainOnly===only));modes.append(b);
  }
  tools.append(modes);
  const viewport=el("div",null,"graph-viewport");
  board.append(viewport);
  const svg=graphSVG("svg",{role:"group",tabindex:"0","aria-label":"Dependency map. Prerequisites above, results below. Use arrow keys to pan."});
  viewport.append(svg);
  const defs=graphSVG("defs"),docURL=location.href.split("#")[0];
  for(const kind of ["ancestor","descendant","other"]){
    const marker=graphSVG("marker",{id:"arrow-"+kind,viewBox:"0 0 10 10",refX:9,refY:5,markerWidth:6,markerHeight:6,orient:"auto"});
    marker.append(graphSVG("path",{d:"M0 0 L10 5 L0 10 Z",class:"arrow-"+kind}));defs.append(marker);
  }
  svg.append(defs);
  const graph=new dagre.graphlib.Graph({multigraph:true}).setGraph({rankdir:"TB",nodesep:22,ranksep:68,marginx:24,marginy:25}).setDefaultEdgeLabel(()=>({}));
  const linked=shown.filter(c=>parents.get(c.id).length || children.get(c.id).length);
  const isolated=shown.filter(c=>!parents.get(c.id).length && !children.get(c.id).length);
  for(const c of linked) graph.setNode(c.id,{width:174,height:72});
  edges.forEach((e,i)=>graph.setEdge(e.prerequisite,e.claim,{},String(i)));
  const bounds={width:0,height:0};
  if(linked.length){
    dagre.layout(graph);
    bounds.width=graph.graph().width;bounds.height=graph.graph().height;
  }
  // Pack isolated claims below the linked components. Dagre places every isolate
  // in one rank, making the whole-paper overview unnecessarily wide.
  if(isolated.length){
    const width=174,height=72,gap=22,margin=24;
    const columns=Math.min(isolated.length,Math.max(1,Math.floor((bounds.width-2*margin+gap)/(width+gap)),Math.ceil(Math.sqrt(isolated.length))));
    const top=bounds.height+margin;
    isolated.forEach((c,i)=>graph.setNode(c.id,{width,height,
      x:margin+width/2+(i%columns)*(width+gap),y:top+height/2+Math.floor(i/columns)*(height+gap)}));
    bounds.width=Math.max(bounds.width,2*margin+columns*(width+gap)-gap);
    bounds.height=top+Math.ceil(isolated.length/columns)*(height+gap)-gap+margin;
  }
  edges.forEach((e,i)=>{
    const kind=(up.has(e.prerequisite)||e.prerequisite===selected.id) && (up.has(e.claim)||e.claim===selected.id)?"ancestor":
      (down.has(e.prerequisite)||e.prerequisite===selected.id) && (down.has(e.claim)||e.claim===selected.id)?"descendant":"other";
    const grounding=e.grounding||"paper";
    const path=graphSVG("path",{class:"graph-edge "+kind+" grounding-"+grounding,d:smoothEdge(graph.edge(e.prerequisite,e.claim,String(i)).points),
      "marker-end":"url("+docURL+"#arrow-"+kind+")"});
    const tip=graphSVG("title");
    const gLabel=e.grounding_label||EDGE_GROUNDING_LABELS[grounding];
    tip.textContent=(grounding!=="paper"&&gLabel?gLabel+" — ":"")+e.reason;
    path.append(tip);svg.append(path);
  });
  for(const c of shown){
    const g=graph.node(c.id);
    const relation=c.id===selected.id?"selected":up.has(c.id)?"ancestor":down.has(c.id)?"descendant":"other";
    const a=graphSVG("a",{href:route(c.id,"english",true),class:"graph-node "+relation,transform:"translate("+(g.x-g.width/2)+" "+(g.y-g.height/2)+")","aria-label":c.reference+" · "+c.title});
    if(c.id===selected.id)a.setAttribute("aria-current","true");
    const tooltip=graphSVG("title");tooltip.textContent=c.reference+" · "+c.title;
    a.append(tooltip,graphSVG("rect",{class:"tile",width:g.width,height:g.height,rx:8}),graphSVG("circle",{class:"node-dot",cx:14,cy:16,r:3.5}));
    const ref=graphSVG("text",{class:"tile-ref",x:25,y:20});ref.textContent=c.reference;a.append(ref);
    nodeTitle(c.title,25).forEach((line,i)=>{
      const t=graphSVG("text",{class:"tile-title",x:11,y:36+i*15});t.textContent=line;a.append(t);
    });
    svg.append(a);
  }
  const key=JSON.stringify([shown.map(c=>[c.id,c.title]),edges.map(e=>[e.claim,e.prerequisite])]);
  if(graphState.layoutKey!==key){graphState.camera=null;graphState.layoutKey=key;}
  const zoom=el("div",null,"graph-zoom"), readout=el("output");
  readout.setAttribute("aria-label","Zoom level");tools.append(zoom);
  function fit(){
    graphState.autoFit=true;
    graphState.camera={x:bounds.width/2,y:bounds.height/2,k:Math.min(viewport.clientWidth/bounds.width,viewport.clientHeight/bounds.height,1.35)};
    paint();
  }
  function paint(){
    const {x,y,k}=graphState.camera,w=viewport.clientWidth/k,h=viewport.clientHeight/k;
    svg.setAttribute("viewBox",[x-w/2,y-h/2,w,h].join(" "));readout.textContent=Math.round(k*100)+"%";
  }
  function zoomBy(scale,pivot){
    graphState.autoFit=false;
    const c=graphState.camera, old=c.k;
    c.k=Math.min(4,Math.max(0.035,old*scale));
    if(pivot){c.x+=pivot.x*(1/old-1/c.k);c.y+=pivot.y*(1/old-1/c.k);}
    paint();
  }
  const minus=graphButton("−",()=>zoomBy(1/1.25)), plus=graphButton("+",()=>zoomBy(1.25));
  minus.setAttribute("aria-label","Zoom out");plus.setAttribute("aria-label","Zoom in");
  zoom.append(minus,readout,plus,graphButton("Fit",fit));
  let drag=null,moved=false;
  svg.onpointerdown=e=>{if(e.button===0){drag={x:e.clientX,y:e.clientY,id:e.pointerId};moved=false;}};
  svg.onpointermove=e=>{
    if(!drag||e.pointerId!==drag.id)return;
    const dx=e.clientX-drag.x,dy=e.clientY-drag.y;
    if(!moved && Math.hypot(dx,dy)<4)return;
    if(!moved){svg.setPointerCapture(e.pointerId);moved=true;graphState.autoFit=false;}
    graphState.camera.x-=dx/graphState.camera.k;graphState.camera.y-=dy/graphState.camera.k;
    drag.x=e.clientX;drag.y=e.clientY;paint();
  };
  svg.onpointerup=svg.onpointercancel=svg.onlostpointercapture=()=>{drag=null;};
  svg.addEventListener("click",e=>{if(moved){e.preventDefault();moved=false;}},true);
  svg.onwheel=e=>{if(!e.ctrlKey&&!e.metaKey)return;e.preventDefault();const b=svg.getBoundingClientRect();
    zoomBy(Math.exp(-e.deltaY*.007),{x:e.clientX-b.left-b.width/2,y:e.clientY-b.top-b.height/2});};
  svg.onkeydown=e=>{
    if(e.key==="+"||e.key==="=") zoomBy(1.25);
    else if(e.key==="-") zoomBy(.8);
    else if(e.key==="Home") fit();
    else if(e.key.startsWith("Arrow")){
      graphState.autoFit=false;
      const step=48/graphState.camera.k;
      if(e.key==="ArrowRight")graphState.camera.x+=step;
      if(e.key==="ArrowLeft")graphState.camera.x-=step;
      if(e.key==="ArrowDown")graphState.camera.y+=step;
      if(e.key==="ArrowUp")graphState.camera.y-=step;
      paint();
    } else return;
    e.preventDefault();
  };
  if(graphState.camera)paint();else fit();
  graphState.resize=new ResizeObserver(()=>{
    if(viewport.isConnected && graphState.camera){if(graphState.autoFit)fit();else paint();}
  });graphState.resize.observe(viewport);
  const legend=el("div",null,"graph-legend");
  for(const [label,key] of [["Selected","selected"],["Prerequisite","ancestor"],["Uses selected claim","descendant"]]){
    const item=el("span",label);item.prepend(el("i",null,key));legend.append(item);
  }
  const hasGrounding=edges.some(e=>e.grounding==="both"||e.grounding==="paper_only"||e.grounding==="lean_only");
  if(hasGrounding){
    for(const [label,key] of [
      ["Used in both paper & Lean proof","edge-swatch grounding-both"],
      ["Paper-only dependency","edge-swatch grounding-paper_only"],
      ["Lean-only prerequisite","edge-swatch grounding-lean_only"],
    ]){
      const item=el("span",label);item.prepend(el("i",null,key));legend.append(item);
    }
  }
  board.append(legend);
  main.append(el("p","Arrows run from a prerequisite to the result that uses it."+
    (isolated.length?" Claims without arrows have no recorded dependencies or dependents.":""),"graph-caption"));

  inspector.append(el("small",selected.reference),el("h3",selected.title),rich(selected.summary||"No English summary recorded."),link("All proofs →",route(selected.id),"graph-read"));
  for(const [reverse,label] of [[false,"Depends on"],[true,"Used by"]]){
    const section=el("div",null,"graph-relation");
    const items=relations(selected,reverse);section.append(el("h4",label+" ("+items.length+")"));
    for(const e of items){
      const c=claims.get(reverse?e.claim:e.prerequisite);
      const row=el("div",null,"graph-edge-item");
      row.append(link(c.reference+" · "+c.title,route(c.id,"english",true)));
      if(e.grounding && e.grounding!=="paper"){
        row.append(el("span",e.grounding_label||EDGE_GROUNDING_LABELS[e.grounding]||e.grounding,"edge-grounding grounding-"+e.grounding));
      }
      row.append(el("p",e.reason));
      section.append(row);
    }
    if(!items.length)section.append(el("p","No recorded links."));
    inspector.append(section);
  }
}
