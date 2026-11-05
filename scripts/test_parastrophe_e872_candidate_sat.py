"""Audit SAT constraints against direct evaluation of small multiplication tables."""
import itertools
import unittest

from pysat.solvers import Solver
from parastrophe_e872_candidate_sat import encode
from parastrophe_e872_compression import Model, core, BASE


def evaluate(table, term, xyz):
    return xyz[term] if isinstance(term,int) else table[evaluate(table,term[0],xyz)][evaluate(table,term[1],xyz)]


class CandidateSatTest(unittest.TestCase):
    def test_every_two_element_table(self):
        for term in (0, (0,1), (1,0), (0,core(0)), BASE):
            for failure in ("unit", "cross", "collision0"):
                cnf, variables = encode(2,term,failure)
                with Solver(name="glucose42",bootstrap_with=cnf) as solver:
                    for entries in itertools.product(range(2),repeat=4):
                        table=[list(entries[:2]),list(entries[2:])]
                        if failure=="unit":
                            bad=evaluate(table,(0,core(0)),(0,0,0))!=0 and table[0][0]==1
                        elif failure=="cross":
                            bad=all(evaluate(table,(0,core(0)),(x,x,x))==x for x in range(2))
                            bad=bad and any(evaluate(table,BASE,(0,y,0))!=0 for y in range(2))
                        else:
                            bad=table[0][0]==table[0][1]
                        expected=Model(table).holds(term) and bad
                        actual=solver.solve(assumptions=[variables[x][y][table[x][y]]
                                                       for x,y in itertools.product(range(2),repeat=2)])
                        self.assertEqual(actual,expected,(term,failure,table))

    def test_block_and_row_restrictions(self):
        # All 256 row-bijective operations preserving two two-element blocks.
        # Compare the compact block encoding with the unrestricted encoding.
        term=(1,(1,0))
        compact, cv=encode(4,term,"unit",block=2)
        general, gv=encode(4,term,"unit",translations="left")
        with Solver(name="glucose42",bootstrap_with=compact) as a, Solver(
                name="glucose42",bootstrap_with=general) as b:
            for flips in itertools.product(range(2),repeat=8):
                table=[[2*(y//2)+((y%2)^flips[2*x+y//2]) for y in range(4)] for x in range(4)]
                expected = (Model(table).holds(term) and table[0][0]==1 and
                            evaluate(table,(0,core(0)),(0,0,0))!=0)
                self.assertEqual(a.solve(assumptions=[cv[x][y][table[x][y]]for x in range(4)for y in range(4)]), expected)
                self.assertEqual(b.solve(assumptions=[gv[x][y][table[x][y]]for x in range(4)for y in range(4)]), expected)

    def test_reject_bad_domains(self):
        with self.assertRaises(ValueError):
            encode(2,BASE,"collision2")
        with self.assertRaises(ValueError):
            encode(5,BASE,"unit",block=2)


if __name__=="__main__":
    unittest.main()
