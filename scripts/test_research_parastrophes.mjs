import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {test} from "node:test";
import {decode} from "../home_page/research/shared.js";
import {FIELDS, parastropheBoard, dualTree, termText} from "../home_page/research/parastrophes.js";
import {cellHTML, overviewHTML, proofHTML} from "../home_page/research/parastrophe-view.js";

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
  "singleEquation_of_equivalent"];
const syntheticIndex = {commit:"test", equations:Array(6).fill("x = x"), duals:[0,2,1,4,3,6,5]};
const base = {version:1,commit:"test",local:false,repository:"example/repo",
  rules:names.map(n=>({name:`Parastrophes.${n}`,file:"rules.lean",line:1,status:"PROVED"}))};
const seed = changes => ({equation:1,scope:"all",kind:"quasigroup",side:null,positive:true,status:"PROVED",
  name:"example",file:"example.lean",line:1,targetEquation:null,targetLaw:null,term:null,description:"",...changes});
const build = (records, implications) => parastropheBoard({...base,records},syntheticIndex,implications);

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
  assert.equal(b.get(3,"all","quasigroup").status,1);
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

test("generated records and provenance",{skip:!data && "Historical bundle has no parastrophe dataset"},async()=>{
  const index=await read("index"), implications={};
  for(const scope of ["all","fin"]) {
    const b=await read(`implies-${scope}`),m=decode(b.status,b.classes*b.classes);
    b.at=(a,c)=>m[b.classOf[a]*b.classes+b.classOf[c]];implications[scope]=b;
  }
  const b=parastropheBoard(data,index,implications);
  for(const name of names) assert.ok(b.ruleRefs.has(name),name);
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
  assert.equal(b.get(543,"all","singleEquation","right").status,2);
  assert.equal(b.get(543,"fin","singleEquation","right").status,0);
  assert.equal(b.get(704,"fin","term","left").status,1);
  assert.equal(b.get(704,"fin","uniformTerm","left").status,0);
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
  assert.ok(q.steps.some(s=>s.rule==="termRecovery_quasigroup" && s.support));
  assert.equal(b.get(1,"fin","uniformTerm","left").status,0);
});
