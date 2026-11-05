#!/usr/bin/env node
// Inventory the generated catalogue using exactly the website's proof closure.
import {readFile} from 'node:fs/promises';
import {decode} from '../home_page/research/shared.js';
import {parastropheBoard, FIELDS} from '../home_page/research/parastrophes.js';
const root = new URL('../home_page/research/data/', import.meta.url);
const read = async name => JSON.parse(await readFile(new URL(`${name}.json`, root), 'utf8'));
const [data, index, all, fin] = await Promise.all(['parastrophes', 'index', 'implies-all', 'implies-fin'].map(read));
const implications = {all, fin};
for (const b of [all, fin]) {
  const matrix = decode(b.status, b.classes * b.classes);
  b.at = (a, c) => matrix[b.classOf[a] * b.classes + b.classOf[c]];
}
const board = parastropheBoard(data, index, implications);
const report = {records: data.records.length, transferRules: data.rules.length, scopes: {}};
for (const scope of ['all', 'fin']) {
  const unknownQuasigroup = [], openRows = [];
  const fields = FIELDS.map(([kind, side]) => ({kind, side, yes: 0, no: 0, unknown: 0, conjectural: 0, notApplicable: 0}));
  for (let eq = 1; eq <= index.equations.length; eq++) {
    if (!board.get(eq, scope, 'quasigroup').status) unknownQuasigroup.push(eq);
    if (board.unproved(eq, scope)) openRows.push(eq);
    for (const f of fields) {
      const status = board.get(eq, scope, f.kind, f.side).status;
      const label = !['quasigroup', 'sideQuasigroup'].includes(f.kind) && !board.applicable(eq, scope, f.side) ? 'notApplicable'
        : ['unknown', 'yes', 'no', 'conjectural', 'conjectural'][status];
      f[label]++;
    }
  }
  report.scopes[scope] = {fullyKnownRows: index.equations.length - openRows.length, unknownQuasigroup, unknownLeft: Array.from({length:index.equations.length},(_,i)=>i+1).filter(n=>!board.get(n,scope,'sideQuasigroup','left').status), unknownRight: Array.from({length:index.equations.length},(_,i)=>i+1).filter(n=>!board.get(n,scope,'sideQuasigroup','right').status), openRows, fields};
}
if (process.argv.includes('--json')) console.log(JSON.stringify(report, null, 2));
else {
  console.log(`${report.records} registered results; ${report.transferRules} checked transfer rules.`);
  for (const [scope, r] of Object.entries(report.scopes)) {
    console.log(`${scope}: ${r.fullyKnownRows}/${index.equations.length} rows fully settled; ${r.unknownQuasigroup.length} quasigroup gaps.`);
    console.log(`One-sided gaps: left ${r.unknownLeft.length}, right ${r.unknownRight.length}.`);
    console.log(`Quasigroup gaps: ${r.unknownQuasigroup.map(n => `E${n}`).join(', ') || 'none'}`);
  }
}
