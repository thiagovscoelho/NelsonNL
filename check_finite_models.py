"""Exhaustive finite checks of the seven displayed NL axioms and two rules.

These checks are independent sanity checks, not a Lean kernel verification.
All triple inequalities are LEFT associated in the order AB, BC, AC.
"""
from itertools import product
import json


def check(n, neg, conj, cons, imp, D):
    def inc(a,b): return neg[cons[a][b]]
    def eqv(a,b): return conj[imp[a][b]][imp[b][a]]
    def neq(a,b): return neg[eqv(a,b)]
    def d3(a,b,c): return conj[conj[neq(a,b)][neq(b,c)]][neq(a,c)]
    failures = {}
    counts = {f"A{i}":0 for i in range(1,8)} | {"MP":0,"Adj":0}
    def test(name, vals, passed):
        counts[name] += 1
        if not passed and name not in failures:
            failures[name] = vals
    for a in range(n):
        test("A1", (a,), imp[a][a] in D)
        test("A3", (a,), imp[a][neg[neg[a]]] in D)
    for a,b in product(range(n), repeat=2):
        test("A2", (a,b), imp[inc(a,b)][inc(b,a)] in D)
        test("A4", (a,b), imp[imp[a][b]][cons[a][b]] in D)
        test("A6", (a,b), eqv(conj[a][b],conj[b][a]) in D)
        test("MP", (a,b), not (a in D and imp[a][b] in D) or b in D)
        test("Adj", (a,b), not (a in D and b in D) or conj[a][b] in D)
    for a,b,c in product(range(n), repeat=3):
        test("A5", (a,b,c), imp[d3(a,b,c)][imp[conj[imp[a][b]][imp[b][c]]][imp[a][c]]] in D)
        test("A7", (a,b,c), imp[imp[conj[a][b]][c]][imp[conj[a][neg[c]]][neg[b]]] in D)
    return {"checks":counts,"total_checks":sum(counts.values()),"failures":failures}

# A two-element model of the calculus with primitive implication.
boolean_neg = [1,0]
boolean_conj = [[0,0],[0,1]]
constant_cons = [[1,1],[1,1]]
material_imp = [[1,1],[0,1]]
primitive = check(2, boolean_neg, boolean_conj, constant_cons, material_imp, {1})
assert not primitive["failures"]
primitive["aristotle_AT1_at_p_0"] = boolean_neg[material_imp[0][boolean_neg[0]]]
assert primitive["aristotle_AT1_at_p_0"] == 0

# Six-element operations from Fazio--Mascella, arXiv:2506.10893v1,
# Example 4.1. We check against the AXIOMS IN THE USER'S QUESTION,
# not merely against those in that paper.
# Values 0,1,2,3,4,5 correspond to a,b,c,d,e,f; D={a,c,e}.
neg6 = [0,1,3,2,5,4]
cons6 = [
 [0,4,4,0,4,0],
 [4,0,4,0,4,0],
 [4,4,4,0,4,4],
 [0,0,0,0,0,0],
 [4,4,4,0,2,0],
 [0,0,4,0,0,0]]
conj6 = [
 [2,1,2,3,2,1],
 [1,3,1,3,1,3],
 [2,1,2,3,2,1],
 [3,3,3,3,3,3],
 [2,1,2,3,2,1],
 [1,3,1,3,1,3]]
imp6 = [[neg6[cons6[a][neg6[b]]] for b in range(6)] for a in range(6)]
defined = check(6,neg6,conj6,cons6,imp6,{0,2,4})
print(json.dumps({"primitive_boolean_model":primitive,"defined_six_element_candidate":defined},indent=2))
