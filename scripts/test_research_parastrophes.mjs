import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {test} from "node:test";
import {decode} from "../home_page/research/shared.js";
import {FIELDS, parastropheBoard, dualTree, termText} from "../home_page/research/parastrophes.js";
import {cellHTML, overviewHTML, proofHTML, consequencesHTML} from "../home_page/research/parastrophe-view.js";

const root = new URL("../home_page/research/data/", import.meta.url);
const read = async name => JSON.parse(await readFile(new URL(`${name}.json`,root),"utf8"));
let data;
try { data = await read("parastrophes"); }
catch(e) { if (e.code !== "ENOENT") throw e; }
// Old deployment bundles remain usable. Synthetic tests still exercise all rules.
const names = ["quasigroup_finite", "singleEquation_finite", "termRecovery_finite", "uniformTermRecovery_finite",
  "quasigroup_dual", "singleEquation_dual", "termRecovery_dual", "uniformTermRecovery_dual",
  "uniform_implies_term", "termRecovery_quasigroup", "termRecovery_iff_uniform_all", "quasigroup_uniform_all", "quasigroup_term_fin",
  "characterizes_quasigroup", "quasigroup_of_implies", "termRecovery_of_implies", "uniformTermRecovery_of_implies",
  "singleEquation_of_equivalent", "characterizes_self", "characterizes_opposite", "sideQuasigroup_finite", "sideQuasigroup_dual",
  "imageBasis_finite", "imageBasis_dual", "imageBasis_of_equivalent",
  "sideQuasigroup_of_implies", "quasigroup_side", "sideQuasigroups_quasigroup", "termRecovery_sideQuasigroup",
  "sideQuasigroup_uniform_all", "sideQuasigroup_term_fin", "characterizes_sideQuasigroup", "characterizes_symm", "characterizes_otherSide"];
const syntheticIndex = {commit:"test", equations:Array(6).fill("x = x"), duals:[0,2,1,4,3,6,5]};
const base = {version:2,commit:"test",local:false,repository:"example/repo",
  rules:names.map(n=>({name:`Parastrophes.${n}`,file:"rules.lean",line:1,status:"PROVED"}))};
const seed = changes => ({equation:1,scope:"all",kind:"quasigroup",side:null,positive:true,status:"PROVED",
  name:"example",file:"example.lean",line:1,targetEquation:null,targetLaw:null,term:null,description:"",...changes});
const build = (records, implications) => parastropheBoard({...base,records},syntheticIndex,implications);

const basisLaw = {lhs:{leaf:0},rhs:{left:{leaf:0},right:{leaf:1}}};
const basisSeed = changes => ({equation:1,scope:"fin",side:"left",status:"PROVED",
  name:"Proof.basis",file:"basis.lean",line:8,targetLaws:[basisLaw,basisLaw],...changes});
test("a finite basis stays separate from the one-equation question",()=>{
  const b=parastropheBoard({...base,records:[],imageBases:[basisSeed({})]},syntheticIndex);
  assert.equal(b.get(1,"fin","singleEquation","left").status,0);
  assert.equal(b.getBasis(1,"fin","left").targetLaws.length,2);
  assert.equal(b.getBasis(1,"all","left"),undefined);
  assert.ok(b.unproved(1,"fin"));
  assert.match(cellHTML(b,1,"fin","singleEquation","left"),/2-equation basis/);
  const html=proofHTML(b,1,"fin","singleEquation","left");
  assert.match(html,/Exact 2-equation characterization/);
  assert.match(html,/Proof.basis/);
  assert.match(html,/single equation suffices remains unproved/);
  assert.deepEqual(b.getBasis(2,"fin","right").targetLaws[0],
    {lhs:dualTree(basisLaw.lhs),rhs:dualTree(basisLaw.rhs)});
  assert.match(proofHTML(b,2,"fin","singleEquation","right"),/imageBasis_dual/);
});
test("shorter finite bases override a longer arbitrary-carrier basis",()=>{
  const all=basisSeed({scope:"all",targetLaws:[basisLaw,basisLaw,basisLaw]});
  for(const imageBases of [[all,basisSeed({})],[basisSeed({}),all]]) {
    const b=parastropheBoard({...base,records:[],imageBases},syntheticIndex);
    assert.equal(b.getBasis(1,"all","left").targetLaws.length,3);
    assert.equal(b.getBasis(1,"fin","left").targetLaws.length,2);
    assert.equal(b.getBasis(2,"fin","right").targetLaws.length,2);
  }
});
test("a partial division image keeps its basis accessible",()=>{
  const b=parastropheBoard({...base,records:[seed({kind:"sideQuasigroup",side:"left",positive:false})],
    imageBases:[basisSeed({scope:"all"})]},syntheticIndex);
  const cell=cellHTML(b,1,"all","singleEquation","left");
  assert.match(cell,/Not applicable/);
  assert.match(cell,/2-equation basis/);
  assert.match(proofHTML(b,1,"all","singleEquation","left"),/source models that admit this division/);
});
test("basis transfer requires equivalence and audited evidence",()=>{
  const board={groups:[[1,3],[2],[4],[5],[6]],classOf:[0,0,1,0,2,3,4],
    at:(a,b)=>a===b || ["1,3","3,1","5,1"].includes(`${a},${b}`) ? 1 : 0};
  const d={...base,records:[],imageBases:[basisSeed({})]};
  const b=parastropheBoard(d,syntheticIndex,{fin:board});
  assert.ok(b.getBasis(3,"fin","left"));
  assert.equal(b.getBasis(5,"fin","left"),undefined);
  assert.equal(b.get(3,"fin","singleEquation","left").status,0);
  assert.match(proofHTML(b,3,"fin","singleEquation","left"),/imageBasis_of_equivalent/);
  assert.throws(()=>parastropheBoard({...d,rules:[]},syntheticIndex),/Missing audited/);
  assert.throws(()=>parastropheBoard({...d,imageBases:[basisSeed({status:"PROOF_AVAILABLE"})]},syntheticIndex),/Invalid image-basis/);
});

test("generated consequences retain scope, direction, counts, and Lean evidence",()=>{
  const refs=[{name:"Proof.image",file:"proof.lean",line:7,status:"PROVED"}];
  const c={name:"Generated.forward",source:1,target:3,scope:"fin",side:"left",refs:["Proof.image"]};
  const d={...base,consequenceSources:refs,consequences:[
    {...c,kind:"termStructural"},{...c,kind:"structural"},{...c,kind:"fineSpectrum"}]};
  const html=consequencesHTML(d,1);
  assert.match(html,/Term-structural/);
  assert.doesNotMatch(html,/FO-structural/);
  assert.match(html,/labelled models and of models up to isomorphism/);
  assert.match(html,/finite carriers/);
  assert.match(html,/Proof.image/);
  assert.match(html,/Generated.forward/);
  assert.equal(consequencesHTML(d,1,"all"),"");
  assert.equal(consequencesHTML(d,1,"fin","right"),"");
  assert.equal(consequencesHTML(d,5),"");
});

test("all-carrier quasigroup laws have uniform terms; finite-only laws need not",()=>{
  const a=build([seed({})]);
  for(const scope of ["all","fin"]) for(const side of ["left","right"]) for(const k of ["term","uniformTerm"])
    assert.equal(a.get(1,scope,k,side).status,1);
  const f=build([seed({scope:"fin"})]);
  assert.equal(f.get(1,"all","quasigroup").status,0);
  for(const side of ["left","right"]) {
    assert.equal(f.get(1,"fin","term",side).status,1);
    assert.equal(f.get(1,"fin","uniformTerm",side).status,0);
  }
});

test("duality changes the side, target equation, and explicit term",()=>{
  const t={left:{leaf:0},right:{left:{leaf:0},right:{leaf:1}}};
  const b=build([seed({kind:"uniformTerm",side:"left",term:t}),
    seed({kind:"singleEquation",side:"left",targetEquation:3,targetLaw:{lhs:t,rhs:{leaf:0}}})]);
  assert.equal(b.get(2,"all","singleEquation","right").targetEquation,4);
  assert.equal(b.get(2,"all","singleEquation","left").status,0);
  assert.deepEqual(b.get(2,"all","uniformTerm","right").term,dualTree(t,true));
  assert.deepEqual(dualTree(dualTree(t,true),true),t);
  assert.equal(b.get(3,"all","sideQuasigroup","left").status,1);
});

test("characterization negatives leave independent term questions available",()=>{
  const b=build([seed({}),seed({kind:"singleEquation",side:"right",positive:false})]);
  assert.equal(b.get(1,"all","singleEquation","right").status,2);
  assert.equal(b.get(1,"fin","singleEquation","right").status,0);
  assert.equal(b.get(1,"all","uniformTerm","right").status,1);
  assert.doesNotMatch(cellHTML(b,1,"all","term","right"),/Not applicable/);
});

test("negative scope and term-strength propagation have the right directions",()=>{
  const b=build([seed({kind:"uniformTerm",side:"left",scope:"fin",positive:false})]);
  assert.equal(b.get(1,"all","uniformTerm","left").status,2);
  assert.equal(b.get(1,"all","term","left").status,2);
  assert.equal(b.get(1,"fin","term","left").status,0);
  assert.equal(b.get(1,"all","quasigroup").status,2);
  assert.equal(b.get(1,"fin","quasigroup").status,0);
  assert.match(cellHTML(b,1,"all","singleEquation","left"),/Not applicable/);
});

test("claims are visible without becoming proved consequences",()=>{
  const b=build([seed({status:"PROOF_AVAILABLE"})]);
  assert.equal(b.get(1,"all","quasigroup").status,3);
  assert.equal(b.get(1,"fin","quasigroup").status,0);
  assert.equal(b.get(1,"all","uniformTerm","left").status,0);
  assert.ok(b.unproved(1,"all"));
  assert.throws(()=>build([seed({}),seed({positive:false})]),/Conflicting/);
});

test("one-way implication cannot transfer an exact characterization",()=>{
  const board={groups:[[1],[2],[3],[4],[5],[6]],classOf:[0,0,1,2,3,4,5],
    at:(a,b)=>a===b || (a===3&&b===1) ? 1 : 0};
  const b=build([seed({}),seed({kind:"singleEquation",side:"left",targetEquation:5})],{all:board});
  assert.equal(b.get(3,"all","quasigroup").status,1);
  assert.equal(b.get(3,"all","singleEquation","left").status,0);
});

test("universal properties move to stronger laws; counterexamples move to weaker laws",()=>{
  // E3 -> E1 -> E5, together with the dual chain E4 -> E2 -> E6.
  const edges=new Set(["3,1","1,5","3,5","4,2","2,6","4,6"]);
  const board={groups:[[1],[2],[3],[4],[5],[6]],classOf:[0,0,1,2,3,4,5],
    at:(a,b)=>a===b || edges.has(`${a},${b}`) ? 1 : 0};
  for(const kind of ["quasigroup","sideQuasigroup","term","uniformTerm"]) {
    const side=kind==="quasigroup" ? null : "left";
    const yes=build([seed({kind,side})],{all:board});
    assert.equal(yes.get(3,"all",kind,side).status,1,`${kind}: stronger law inherits yes`);
    assert.equal(yes.get(5,"all",kind,side).status,0,`${kind}: weaker law remains open`);
    const no=build([seed({kind,side,positive:false})],{all:board});
    assert.equal(no.get(5,"all",kind,side).status,2,`${kind}: weaker law inherits counterexample`);
    assert.equal(no.get(3,"all",kind,side).status,0,`${kind}: stronger law remains open`);
  }
  // A bare failure to characterize one image class need not survive enlarging it.
  const noImage=build([seed({kind:"singleEquation",side:"left",positive:false})],{all:board});
  assert.equal(noImage.get(3,"all","singleEquation","left").status,0);
  assert.equal(noImage.get(5,"all","singleEquation","left").status,0);
});

test("generated records and provenance",{skip:!data && "Historical bundle has no parastrophe dataset"},async()=>{
  const index=await read("index"), implications={};
  for(const scope of ["all","fin"]) {
    const b=await read(`implies-${scope}`),m=decode(b.status,b.classes*b.classes);
    b.at=(a,c)=>m[b.classOf[a]*b.classes+b.classOf[c]];implications[scope]=b;
  }
  const b=parastropheBoard(data,index,implications);
  for(const name of names.filter(n => data.imageBases || !n.startsWith("imageBasis_")))
    assert.ok(b.ruleRefs.has(name),name);
  for(const record of data.imageBases || []) {
    const basis=b.getBasis(record.equation,record.scope,record.side);
    assert.ok(basis.targetLaws.length<=record.targetLaws.length);
    assert.match(proofHTML(b,record.equation,record.scope,"singleEquation",record.side),
      /Exact [23]-equation characterization/);
  }
  for(const [key,cell] of b.cells) {
    const r=data.records[cell.seed];
    assert.equal(r.status,"PROVED",key);
    for(const step of cell.steps) {
      assert.equal(b.ruleRefs.get(step.rule).status,"PROVED");
      if(step.rule.endsWith("_of_implies") || step.equivalent) {
        const board=implications[step.scope];
        if(step.equivalent || step.positive) assert.equal(board.at(step.to,step.from),1);
        if(step.equivalent || !step.positive) assert.equal(board.at(step.from,step.to),1);
      }
    }
  }
  for(const scope of ["all","fin"]) {
    for(const [kind,side] of FIELDS) assert.equal(b.get(14,scope,kind,side).status,1);
    assert.equal(b.get(1,scope,"quasigroup").status,2);
    assert.equal(b.get(3,scope,"quasigroup").status,2);
    assert.equal(b.get(543,scope,"uniformTerm","right").status,1);
  }
  // Integral companion families give genuine negatives, independently of term recovery.
  if (data.records.some(r=>r.name.endsWith("left_noSingleEquation670_fin"))) {
    for (const n of [670,676,704,713,870,1076,1083,1285,1288,1313,2294,2531]) {
      const record=data.records.find(r=>r.name.endsWith(`left_noSingleEquation${n}_fin`));
      assert.equal(record.status,"PROVED");
      for (const scope of ["all","fin"]) {
        assert.equal(b.get(n,scope,"singleEquation","left").status,2,`E${n} ${scope}`);
        assert.equal(b.get(index.duals[n],scope,"singleEquation","right").status,2);
      }
    }
    assert.match(proofHTML(b,704,"fin","singleEquation","left"),/HigherDegreeImageObstructions/);
  }
  assert.equal(b.get(543,"all","singleEquation","right").status,2);
  assert.equal(b.get(543,"fin","singleEquation","right").status,2);
  assert.equal(b.get(704,"fin","term","left").status,1);
  assert.equal(b.get(704,"fin","uniformTerm","left").status,1);
  assert.equal(b.get(704,"fin","uniformTerm","right").status,1);
  assert.equal(termText(b.get(543,"all","uniformTerm","left").term),"(x ◇ y)");
  assert.match(overviewHTML(b,543),/parastrophes\/\?eq=543/);
  assert.match(proofHTML(b,543,"all","singleEquation","right"),/right_noSingleEquation543/);
  assert.match(proofHTML(b,543,"all","uniformTerm","right"),/Division term/);
  assert.doesNotMatch(overviewHTML(b,543),/undefined|NaN/);
});

test("both division terms supply quasigroup status with both premises recorded",()=>{
  const b=build([seed({kind:"term",scope:"fin",side:"left"}),seed({kind:"term",scope:"fin",side:"right"})]);
  const q=b.get(1,"fin","quasigroup");
  assert.equal(q.status,1);
  assert.ok(q.steps.some(s=>s.rule==="sideQuasigroups_quasigroup" && s.support));
  assert.equal(b.get(1,"fin","uniformTerm","left").status,0);
});

test("self and opposite divisions give exact images with only the indicated division",()=>{
  const self={left:{leaf:0},right:{leaf:1}}, opposite={left:{leaf:1},right:{leaf:0}};
  const noQ=build([seed({kind:"uniformTerm",side:"left",term:self})]);
  assert.equal(noQ.get(1,"all","singleEquation","left").status,1);
  assert.equal(noQ.get(1,"all","quasigroup").status,0);
  for(const [term,target] of [[self,1],[opposite,2]]) {
    const b=build([seed({}),seed({kind:"uniformTerm",side:"left",term})]);
    assert.equal(b.get(1,"all","singleEquation","left").targetEquation,target);
    assert.equal(b.get(1,"fin","singleEquation","left").status,1);
    assert.equal(b.get(1,"all","singleEquation","left").steps.at(-1).rule,
      target === 1 ? "characterizes_self" : "characterizes_opposite");
  }
});

test("concrete terms survive earlier generic existence and propagate to stronger laws",()=>{
  const table={groups:[[1],[2],[3],[4],[5],[6]],classOf:[0,0,1,2,3,4,5],
    at:(a,b)=>a===b || (a===1&&b===3) || (a===2&&b===4) ? 1 : 0};
  const term={left:{leaf:0},right:{leaf:1}};
  const b=build([seed({}),seed({equation:3,kind:"uniformTerm",side:"left",term})],{all:table,fin:table});
  for(const scope of ["all","fin"]) for(const kind of ["term","uniformTerm"])
    assert.deepEqual(b.get(1,scope,kind,"left").term,term);
  // E1 has its own exact image law, not E3's image law transferred one way.
  assert.equal(b.get(1,"all","singleEquation","left").targetEquation,1);
  assert.match(proofHTML(b,1,"all","singleEquation","left"),/Exact characterizing equation/);
});

test("populated catalogue keeps finite and infinite conclusions distinct",
  {skip:!data?.records.some(r=>r.name.endsWith("not_quasigroup63_all")) && "Historical dataset"},async()=>{
  const index=await read("index"),bs={};
  for(const scope of ["all","fin"]){const b=await read(`implies-${scope}`),m=decode(b.status,b.classes*b.classes);
    b.at=(a,c)=>m[b.classOf[a]*b.classes+b.classOf[c]];bs[scope]=b;}
  const b=parastropheBoard(data,index,bs);
  for(const n of [63,115,477,481,680,1516]) {
    assert.equal(b.get(n,"all","quasigroup").status,2,`E${n} all`);
    assert.equal(b.get(n,"fin","quasigroup").status,1,`E${n} finite`);
  }
  for(const n of [474,501,670]) for(const scope of ["all","fin"])
    assert.equal(b.get(n,scope,"quasigroup").status,2);
  assert.equal(b.get(63,"fin","singleEquation","left").targetEquation,125);
  assert.equal(b.get(125,"fin","singleEquation","left").targetEquation,63);
  assert.equal(b.get(546,"all","singleEquation","left").targetEquation,556);
  assert.equal(b.get(556,"all","singleEquation","left").targetEquation,546);
  for(const n of [880,1719]) assert.equal(b.get(n,"all","quasigroup").status,1);
  assert.equal(b.get(677,"fin","uniformTerm","left").status,1);
  assert.equal(b.get(677,"fin","quasigroup").status,2);
  assert.equal(b.get(677,"all","quasigroup").status,2);
  for(const n of [63,667]) for(const side of ["left","right"])
    assert.ok(b.get(n,"fin","uniformTerm",side).term);
  for(const n of [4,16,670]) {
    const side=n===4 ? "right" : "left", other=n===4 ? "left" : "right";
    assert.equal(b.get(n,"fin","sideQuasigroup",side).status,1);
    assert.equal(b.get(n,"fin","sideQuasigroup",other).status,2);
    assert.doesNotMatch(cellHTML(b,n,"fin","uniformTerm",side),/Not applicable/);
  }
  assert.equal(b.get(4,"all","singleEquation","right").targetEquation,4);
  assert.equal(b.get(16,"all","singleEquation","left").targetEquation,16);
  assert.equal(b.get(1518,"fin","sideQuasigroup","left").status,1);
  assert.equal(b.get(1518,"fin","term","left").status,1);
  assert.equal(b.get(1518,"fin","uniformTerm","left").status,0);
  assert.equal(b.get(1518,"fin","sideQuasigroup","right").status,2);
  assert.ok(b.unproved(1518,"fin"));
  assert.equal(b.get(1525,"fin","sideQuasigroup","left").status,1);
  assert.equal(b.get(1793,"all","sideQuasigroup","left").status,1);
  assert.ok(b.get(1793,"all","uniformTerm","left").term);
  for(const n of [72,75,117,127,501,510,513,703,716,910,916,1122,1325,1525]) {
    assert.equal(b.get(n,"all","sideQuasigroup","left").status,1);
    assert.ok(b.get(n,"all","uniformTerm","left").term);
  }
  for(const [a,t] of [[65,65],[68,68],[464,511],[511,464],[466,466],
    [469,469],[474,474],[476,503],[503,476],[501,501]])
    assert.equal(b.get(a,"fin","singleEquation","left").targetEquation,t);
  for(const n of [75,513,528,562])
    assert.equal(b.get(n,"all","singleEquation","left").targetEquation,n);
  for(const n of [511,917,1117,1289,1323,1491]) {
    assert.equal(b.get(n,"all","sideQuasigroup","left").status,2);
    assert.equal(b.get(n,"fin","sideQuasigroup","left").status,1);
  }
  assert.equal(b.get(1518,"all","sideQuasigroup","left").status,2);
  for(const n of [543,917,978,1113,1117,1152,1658,1670,1673,1876,2444,2447]) {
    assert.equal(b.get(n,"fin","singleEquation","right").status,2);
    assert.equal(b.get(index.duals[n],"fin","singleEquation","left").status,2);
  }
  assert.match(proofHTML(b,543,"fin","singleEquation","right"),/right_noSingleEquation543_fin/);
  for(const n of [68,469,138,510])
    assert.equal(b.get(n,"all","singleEquation","left").targetEquation,n);
  for(const n of [65,476,504,713,1112]) {
    assert.equal(b.get(n,"all","sideQuasigroup","left").status,2);
    assert.equal(b.get(n,"fin","sideQuasigroup","left").status,1);
  }
  for(const n of [1076,1110,1276]) {
    assert.equal(b.get(n,"all","quasigroup").status,2);
    assert.equal(b.get(n,"fin","quasigroup").status,1);
    // Separate countermodel arguments now identify failures on both sides.
    for(const side of ["left","right"])
      assert.equal(b.get(n,"all","sideQuasigroup",side).status,2);
  }
  for(const n of [1525,1586,2291,2294,2301,2328,2497,2504,2531,2734,2903,3103]) {
    const t=b.get(n,"fin","uniformTerm","left");
    assert.equal(t.status,1,`E${n} finite left division`);
    assert.ok(t.term,`E${n} exports a concrete term`);
    assert.ok(b.get(index.duals[n],"fin","uniformTerm","right").term);
  }
  assert.ok(b.get(464,"fin","uniformTerm","right").term);
  for(const n of [1516,2091,3140]) {
    assert.equal(b.get(n,"fin","uniformTerm","left").status,1);
    assert.ok(b.get(n,"fin","uniformTerm","left").term);
  }
  // E1518's new finite bijectivity proof gives per-model terms, but has not
  // supplied a uniform term. Its dual has the same gap on the other side.
  for(let n=1;n<=index.equations.length;n++) for(const side of ["left","right"])
    if(b.get(n,"fin","sideQuasigroup",side).status===1)
      assert.equal(b.get(n,"fin","uniformTerm",side).status,
        (n===1518 && side==="left") || (n===index.duals[1518] && side==="right") ? 0 : 1,
        `E${n} finite ${side}`);
  assert.equal(b.get(692,"all","singleEquation","left").targetEquation,692);
  assert.equal(b.get(898,"all","singleEquation","left").targetEquation,1368);
  assert.equal(b.get(1368,"all","singleEquation","left").targetEquation,898);
  // Longer targets retain their term trees, proof links, and dual/finite transfers.
  for (const scope of ["all", "fin"]) {
    const image703=b.get(703,scope,"singleEquation","left");
    assert.equal(image703.status,1);
    assert.equal(image703.targetEquation,null);
    assert.equal(termText(image703.targetLaw.rhs).match(/◇/g).length,8);
    assert.match(proofHTML(b,703,scope,"singleEquation","left"),/Equation703Image/);
    assert.equal(b.get(index.duals[703],scope,"singleEquation","right").status,1);
  }
  assert.equal(b.get(1518,"fin","singleEquation","left").targetEquation,1518);
  assert.equal(b.get(index.duals[1518],"fin","singleEquation","right").targetEquation,index.duals[1518]);
  assert.match(proofHTML(b,1518,"fin","singleEquation","left"),/SquareImages/);
  const image125=b.get(125,"all","singleEquation","left");
  assert.equal(image125.status,1);
  assert.equal(image125.targetEquation,null);
  assert.equal(termText(image125.targetLaw.rhs).match(/◇/g).length,11);
  assert.match(proofHTML(b,125,"all","singleEquation","left"),/Equation125Image/);
  assert.equal(b.get(index.duals[125],"all","singleEquation","right").status,1);
  // The finite image remains E63; the stronger infinite image does not
  // incorrectly supply left division to every infinite E63 model.
  assert.equal(b.get(125,"fin","singleEquation","left").targetEquation,63);
  assert.equal(b.get(63,"all","sideQuasigroup","left").status,2);
  assert.equal(b.get(63,"all","singleEquation","left").targetEquation,125);
  for (const scope of ["all", "fin"]) {
    for (const [n, operations, module] of [[695,8,"Equation695Image"],
      [1710,8,"Equation695Image"], [1586,6,"Equation1586Image"],
      [1370,21,"Equation1370Image"], [2203,21,"Equation1370Image"]]) {
      const result=b.get(n,scope,"singleEquation","left");
      assert.equal(result.status,1,`E${n} ${scope} exact image`);
      assert.equal(result.targetEquation,null);
      assert.equal(termText(result.targetLaw.rhs).match(/◇/g).length,operations);
      assert.match(proofHTML(b,n,scope,"singleEquation","left"),new RegExp(module));
      assert.equal(b.get(index.duals[n],scope,"singleEquation","right").status,1);
    }
    for (const n of [1278,1325,1387,2137,2152]) {
      assert.equal(b.get(n,scope,"singleEquation","left").status,2);
      assert.match(proofHTML(b,n,scope,"singleEquation","left"),/PatchedSubtraction/);
      assert.equal(b.get(index.duals[n],scope,"singleEquation","right").status,2);
    }
    assert.equal(b.get(1525,scope,"singleEquation","left").status,2);
    assert.match(proofHTML(b,1525,scope,"singleEquation","left"),/TrialityCore/);
    assert.equal(b.get(index.duals[1525],scope,"singleEquation","right").status,2);
    assert.equal(b.get(1525,scope,"uniformTerm","left").status,1);
    for (const [n,side] of [[882,"left"],[907,"left"],[907,"right"]]) {
      assert.equal(b.get(n,scope,"singleEquation",side).status,2);
      assert.match(proofHTML(b,n,scope,"singleEquation",side),
        new RegExp(`Equation${n}ImageObstruction`));
      assert.equal(b.get(index.duals[n],scope,"singleEquation",
        side==="left" ? "right" : "left").status,2);
    }
  }
  for(const scope of ["all","fin"]) {
    for(const n of [127,716]) assert.equal(b.get(n,scope,"singleEquation","left").status,2);
    assert.equal(b.get(870,scope,"singleEquation","right").status,2);
  }
  // E870 has both divisions in every finite model, although its right image
  // admits no single-equation characterization.
  assert.equal(b.get(870,"fin","sideQuasigroup","right").status,1);
  assert.equal(b.get(870,"fin","uniformTerm","right").status,1);
  assert.equal(b.get(870,"fin","quasigroup").status,1);
  for(const n of [677,907]) {
    assert.equal(b.get(n,"all","sideQuasigroup","left").status,2);
    assert.equal(b.get(n,"all","sideQuasigroup","right").status,2);
    assert.equal(b.get(n,"all","quasigroup").status,2);
    assert.equal(b.get(n,"fin","sideQuasigroup","left").status,1);
    assert.equal(b.get(n,"fin","sideQuasigroup","right").status,n===677 ? 2 : 0);
  }
  // An obstruction to characterizing the actual image does not settle
  // whether every E907 model possesses that division in the first place.
  assert.equal(b.get(907,"fin","uniformTerm","left").status,1);
  assert.equal(b.get(907,"fin","term","right").status,0);
  assert.equal(b.get(907,"fin","uniformTerm","right").status,0);
  // The imported finite E677 witness also settles its dual, while keeping
  // the existing left division and its uniform term available.
  const dual677=index.duals[677];
  assert.equal(b.get(dual677,"fin","quasigroup").status,2);
  assert.equal(b.get(dual677,"fin","sideQuasigroup","left").status,2);
  assert.equal(b.get(dual677,"fin","uniformTerm","right").status,1);
  assert.match(proofHTML(b,677,"fin","sideQuasigroup","right"),
    /not_rightQuasigroup677_fin/);
  assert.match(cellHTML(b,677,"fin","uniformTerm","right"),/Not applicable/);
  for(const n of [690,1353])
    assert.equal(b.get(n,"all","uniformTerm","left").status,1);
  for(const n of [466,474,503,676,679,704,706,872,882,1119,1279,1312]) {
    assert.equal(b.get(n,"all","sideQuasigroup","left").status,2,`E${n} all`);
    assert.equal(b.get(n,"fin","sideQuasigroup","left").status,1,`E${n} finite`);
  }
  for(const n of [704,1279]) {
    assert.equal(b.get(n,"all","sideQuasigroup","right").status,2);
    assert.equal(b.get(n,"all","quasigroup").status,2);
    assert.equal(b.get(n,"fin","quasigroup").status,1);
  }
  // Infinite idempotent countermodels do not change the finite Latin theorems.
  for(const source of [667,870,1083,1286,1313]) for(const n of [source,index.duals[source]]) {
    assert.equal(b.get(n,"all","quasigroup").status,2,`E${n} infinite countermodel`);
    assert.equal(b.get(n,"fin","quasigroup").status,1,`E${n} finite Latin theorem`);
    for(const side of ["left","right"])
      assert.equal(b.get(n,"all","sideQuasigroup",side).status,2,`E${n} ${side}`);
  }
  for(const n of [1113,1117]) {
    assert.equal(b.get(n,"all","sideQuasigroup","right").status,2);
    assert.equal(b.get(n,"fin","sideQuasigroup","right").status,1);
  }
  // These countable countermodels distinguish the finite and arbitrary
  // translation statuses, and their duals must acquire the opposite-side fact.
  for (const n of [670,1082,1085,1288,1315,1322]) {
    assert.equal(b.get(n,"all","sideQuasigroup","left").status,2,`E${n} countable collision`);
    assert.equal(b.get(n,"fin","sideQuasigroup","left").status,1,`E${n} finite bijectivity`);
    assert.equal(b.get(index.duals[n],"all","sideQuasigroup","right").status,2);
    assert.match(proofHTML(b,n,"all","sideQuasigroup","left"),/RemainingInfinite/);
  }
  // Matrix families exclude all identities for these images. The opposite
  // division can still have an exact characterization and explicit terms.
  for(const [n,side] of [[115,"left"],[118,"left"],[124,"left"],
    [125,"right"],[63,"right"],[667,"left"],[667,"right"],[467,"right"]]) {
    for(const scope of ["all","fin"])
      assert.equal(b.get(n,scope,"singleEquation",side).status,2,`E${n} ${scope} ${side} image`);
    const dual=index.duals[n], other=side==="left" ? "right" : "left";
    assert.equal(b.get(dual,"fin","singleEquation",other).status,2);
  }
  // Free-group triangles settle both arbitrary-carrier images. Additive and
  // noncommutative finite trades now settle both finite images and their duals.
  for (const n of [1719,1888]) for (const side of ["left","right"]) {
    assert.equal(b.get(n,"all","singleEquation",side).status,2);
    assert.equal(b.get(n,"fin","singleEquation",side).status,2);
    const sourceSide=n===1719 ? side : (side==="left" ? "right" : "left");
    assert.match(proofHTML(b,n,"fin","singleEquation",side),
      new RegExp(`${sourceSide}_noSingleEquation1719_fin`));
    assert.equal(b.get(n,"all","sideQuasigroup",side).status,1);
    assert.equal(b.get(n,"all","uniformTerm",side).status,1);
    assert.match(proofHTML(b,n,"all","singleEquation",side),/Equation1719ImageObstruction/);
  }
  for(const n of [1719,1888]) assert.equal(b.unproved(n,"fin"),false);
  assert.equal(b.get(125,"fin","singleEquation","left").status,1);
  assert.equal(b.get(63,"fin","singleEquation","left").status,1);
  assert.equal(b.get(125,"all","uniformTerm","right").status,1);

});


test("a two-sided negative does not say which side fails",()=>{
  const b=build([seed({positive:false})]);
  assert.equal(b.get(1,"all","sideQuasigroup","left").status,0);
  assert.equal(b.get(1,"all","sideQuasigroup","right").status,0);
  assert.ok(b.unproved(1,"all"));
  assert.doesNotMatch(cellHTML(b,1,"all","term","left"),/Not applicable/);
});

test("one bijective side plus a two-sided counterexample refutes only the other side",()=>{
  const b=build([seed({positive:false,scope:"fin"}),
    seed({kind:"sideQuasigroup",side:"left",scope:"fin"})]);
  assert.equal(b.get(1,"fin","sideQuasigroup","right").status,2);
  assert.equal(b.get(1,"fin","term","left").status,1);
  assert.equal(b.get(1,"fin","uniformTerm","left").status,0);
  assert.doesNotMatch(cellHTML(b,1,"fin","term","left"),/Not applicable/);
  assert.match(cellHTML(b,1,"fin","term","right"),/Not applicable/);
  assert.equal(b.get(2,"fin","sideQuasigroup","right").status,1);
  assert.equal(b.get(2,"fin","sideQuasigroup","left").status,2);
});

test("exact image forces only its own side; reverse uses the source side premise",()=>{
  const record=seed({kind:"singleEquation",side:"left",targetEquation:3});
  const b=build([record]);
  assert.equal(b.get(3,"all","sideQuasigroup","left").status,1);
  assert.equal(b.get(3,"all","quasigroup").status,0);
  assert.equal(b.get(3,"all","singleEquation","left").status,0);
  const c=build([record,seed({kind:"sideQuasigroup",side:"left"})]);
  assert.equal(c.get(3,"all","singleEquation","left").targetEquation,1);
  assert.ok(c.get(3,"all","singleEquation","left").steps.some(s=>s.rule==="characterizes_symm"&&s.support));
  assert.equal(c.get(3,"all","quasigroup").status,0);
});


test("exact one-sided correspondences preserve a counterexample on the other side",()=>{
  const b=build([seed({kind:"singleEquation",side:"left",targetEquation:3}),
    seed({kind:"sideQuasigroup",side:"left"}),
    seed({kind:"sideQuasigroup",side:"right",positive:false})]);
  assert.equal(b.get(3,"all","sideQuasigroup","left").status,1);
  assert.equal(b.get(3,"all","sideQuasigroup","right").status,2);
  const f=b.get(3,"all","sideQuasigroup","right");
  assert.ok(f.steps.some(s=>s.rule==="characterizes_otherSide" && s.supports.length===2));
  assert.match(proofHTML(b,3,"all","sideQuasigroup","right"),/Additional premise/);
});
