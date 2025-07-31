import random
import time
from collections import deque, defaultdict


class Clause:
    def __init__(self, vl):
        self._vars = [v for v in vl]
        self._val = None

    def eval(self, m):
        unknowns = 0
        for v in self._vars:
            val = m[abs(v)]
            if val is None:
                unknowns += 1
            elif (v > 0 and val) or (v < 0 and not val):
                return True
        return False if unknowns == 0 else None

    def isUnit(self, m):
        unassigned = [v for v in self._vars if m[abs(v)] is None]
        if len(unassigned) == 1:
            for v in self._vars:
                val = m[abs(v)]
                if val is not None:
                    if (v > 0 and not val) or (v < 0 and val):
                        continue
                    else:
                        return False
            return True
        return False

    def getUnitLiteral(self, m):
        for v in self._vars:
            if m[abs(v)] is None:
                return v
        return None

    def __repr__(self):
        return f"Clause({self._vars})"


class Assignment:
    def __init__(self, var, val, level, antecedent=None):
        self.var = var
        self.val = val
        self.level = level
        self.antecedent = antecedent  # Clause that implied this assignment


def pickBranchingLiteral(f, m):
    counts = {}
    for clause in f:
        for v in clause._vars:
            if m[abs(v)] is None:
                counts[v] = counts.get(v, 0) + 1
    if not counts:
        return None
    return max(counts, key=counts.get)


def propagate(f, m, trail, level):
    queue = deque([a for a in trail if a.level == level])
    while queue:
        a = queue.popleft()
        for clause in f:
            if clause.eval(m) is False:
                if all(m[abs(v)] is not None for v in clause._vars):
                    return clause
            elif clause.isUnit(m):
                lit = clause.getUnitLiteral(m)
                if lit is not None:
                    var = abs(lit)
                    val = lit > 0
                    if m[var] is not None:
                        if m[var] != val:
                            return clause
                        continue
                    m[var] = val
                    assign = Assignment(var, val, level, clause)
                    trail.append(assign)
                    queue.append(assign)
    return None


def analyze(conflict_clause, trail, level):
    learned = []
    seen = set()
    counter = 0
    clause = conflict_clause
    learned_lits = []
    path = []

    # Count decision-level literals in conflict clause
    for lit in clause._vars:
        var = abs(lit)
        assign = next((a for a in reversed(trail) if a.var == var), None)
        if assign and assign.level == level:
            counter += 1
        seen.add(var)

    i = len(trail) - 1
    while counter > 1:
        while trail[i].var not in seen:
            i -= 1
        assign = trail[i]
        i -= 1

        if assign.antecedent is None:
            continue

        clause = assign.antecedent
        for lit in clause._vars:
            v = abs(lit)
            if v not in seen:
                seen.add(v)
                assign_v = next((a for a in reversed(trail) if a.var == v), None)
                if assign_v and assign_v.level == level:
                    counter += 1
        counter -= 1

    learned_lits = []
    max_other_level = 0
    for var in seen:
        assign = next((a for a in reversed(trail) if a.var == var), None)
        if assign:
            lit = var if not assign.val else -var
            learned_lits.append(lit)
            if assign.level != level:
                max_other_level = max(max_other_level, assign.level)

    return Clause(learned_lits), max_other_level



def backtrack(trail, m, level):
    while trail and trail[-1].level > level:
        a = trail.pop()
        m[a.var] = None


def assign_literal(lit, level, m, trail):
    var = abs(lit)
    val = lit > 0
    m[var] = val
    trail.append(Assignment(var, val, level))


def cdcl(f, numvars):
    m = [None for _ in range(numvars + 1)]
    trail = []
    level = 0

    while True:
        conflict = propagate(f, m, trail, level)
        if conflict:
            if level == 0:
                return False, None
            learned_clause, back_level = analyze(conflict, trail, level)
            backtrack(trail, m, back_level)
            f.append(learned_clause)
            level = back_level
            assign_literal(learned_clause.getUnitLiteral(m), level, m, trail)
        else:
            if all(v is not None for v in m[1:]):
                return True, m
            lit = pickBranchingLiteral(f, m)
            if lit is None:
                return True, m
            level += 1
            assign_literal(lit, level, m, trail)


def loadCNFFile(fn):
    numvars = 0
    numclauses = 0
    clauses = []
    with open(fn, 'r') as fs:
        for line in fs:
            if line.startswith('%'):
                break
            if line.startswith('p'):
                numvars = int(line.split()[2])
                numclauses = int(line.split()[3])
                continue
            if line.startswith('c'):
                continue
            tmp = list(map(int, line.strip().split()))
            tmp = tmp[:-1]  # Remove trailing 0
            clauses.append(Clause(tmp))
            for v in tmp:
                assert abs(v) <= numvars
    assert len(clauses) == numclauses
    return numvars, clauses


def parse_cnf_file(filepath):
    clauses = []
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', 'p', '%', '0')):
                continue
            clause = list(map(int, line.split()))
            if clause and clause[-1] == 0:
                clause.pop()
            clauses.append(clause)
    return clauses

def is_clause_satisfied(clause, assignment_set):
    for literal in clause:
        if literal in assignment_set:
            return True
    return False

def is_cnf_satisfied(cnf_file, assignment):
    # assignment is a list like [1, -2, 3] meaning:
    # x1=True, x2=False, x3=True
    clauses = parse_cnf_file(cnf_file)
    assignment_set = set(assignment)
    for clause in clauses:
        if not is_clause_satisfied(clause, assignment_set):
            return False
    return True

# Example usage


# Main logic
if __name__ == '__main__':
    import argparse
    import sys
    ap = argparse.ArgumentParser()
    ap.add_argument("-c", "--cnf", type=str, default="", help='<cnf file>')
    args, unknown = ap.parse_known_args()  # <--- This prevents crash from unknown args
    import time
    if args.cnf != "":
        print(f"CNF file  : {args.cnf}")
        numvars, clauses = loadCNFFile(args.cnf)
        m = [None for i in range(numvars + 1)]
        t1 = time.time()
        ret, m = cdcl(clauses, numvars)
        t2 = time.time()
        if ret:
            print("SAT")
            print("Prints True with a \"-\" sign and False normally as given in slides")
            a = ([(-i if m[i] == True else i) for i in range(1, len(m))])
            print(a)
            print(t2-t1)
            assignment = a
            for i in range(0,len(assignment)):
                assignment[i]*=-1
            result = is_cnf_satisfied(args.cnf, assignment)
            print("SATISFIED" if result else "NOT SATISFIED")
        else:
            print("UNSAT")
        

