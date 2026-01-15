# %%
from pysat.formula import CNF
from pysat.solvers import Solver
from itertools import permutations
from disjoint_set import DisjointSet
import time
import sys

# prohození pozic pro funkce pro generování permutací
def swap_positions(p, i, j):
    p = list(p)
    p[i], p[j] = p[j], p[i]
    return p

# všechny permutace
def all_perm(n):
    return list(permutations(range(n)))

# transpozice
def transpositions(n):
    idp = list(range(n))
    result = []
    for i in range(n):
        for j in range(i+1, n):
            result.append(swap_positions(idp, i, j))
    return result

# transpozice sousedících hodnot
def neighbors(n):
    idp = list(range(n))
    result = []
    for i in range(n - 1):
        result.append(swap_positions(idp, i, i + 1))
    return result

# dvouprvkový generátor grupy permutací
def gen2(n):
    result = [list((i+1) % n for i in range(n))]
    result.append(swap_positions(list(range(n)), 0, 1))
    return result


# %%
# vytvoření matice s proměnnými
def get_matrix(m, n):
    variables = []
    idx = 1
    for i in range(m):
        variables.append([])
        for j in range(n):
            variables[i].append(idx)
            idx = idx + 1
    return variables
    
# zpermutování matice pomocí zadaných permutací řádků a sloupců
def get_perm(matrix, pi_r, pi_c):
    m = len(matrix)
    n = len(matrix[0])
    varperm = [[0 for _ in range(n)] for _ in range(m)]
    for i in range(m):
        for j in range(n):
            varperm[pi_r[i]][pi_c[j]] = matrix[i][j]
    return varperm

# klauzule získané z porovnání zpermutované (parametr b) a nezpermutované (parametr a) matice proměnných
def get_clauses(a, b, kmax, aux):
    clauses = []
    
    for i in range(len(a)):
        if i >= kmax:
            break
        clause = [-a[i],b[i]]

        # množiny rovnajících se proměnných 
        ds = DisjointSet()
        ds.union('o', b[i])
        ds.union('i', a[i])
        
        # True pokud nastane 0=1
        wrong = False
        
        if i > 0:
            for k in range(i):
                if a[k] != b[k]:
                    ds.union(a[k], b[k])
                    if ds.connected('o', 'i'):
                        wrong = True
                        break
                    try:
                        # pokud pro danou nerovnost již existuje proměnná navíc
                        clause.append(aux[f"{a[k]} {b[k]}"])
                    except:     
                        # pokud pro danou nerovnost ještě proměnná navíc neexistuje
                        clause.append(aux["curr"])                    
                        aux[f"{a[k]} {b[k]}"] = aux["curr"]
                        aux[f"{b[k]} {a[k]}"] = aux["curr"]
                        clauses.append([-aux["curr"],a[k],b[k]])
                        clauses.append([-aux["curr"],-a[k],-b[k]])
                        clauses.append([aux["curr"],-a[k],b[k]])
                        clauses.append([aux["curr"],a[k],-b[k]])
                        aux["curr"] = aux["curr"] + 1
        if ds.connected('o', 'i') or wrong:
            continue
    
        clauses.append(clause)
    return clauses, aux

# klauzule pro všechny zadané permutace
def symmetry_clauses(matrix, symtype, perms, kmax):
    if kmax == 0:
        return []
    m = len(matrix)
    n = len(matrix[0])
    
    # identita (zvlášť pro řadky a sloupce)
    idpr = list(range(m))
    idpc = list(range(n))
    
    clauses = []

    # slovník s proměnnými navíc + na "curr" uložena nejnižší volná proměnná
    aux = {"curr" : m*n+1}

    # permutace pouze na řádcích
    if symtype == "r":
        row = perms(m)
        
        for p in row:
            perm = get_perm(matrix, p, idpc)
            
            a = []
            b = []  
            for i in range(len(matrix)):
                a = a + matrix[i]
                b = b + perm[i]
                
            cls = get_clauses(a, b, kmax, aux)
            clauses += cls[0]
            aux = cls[1]

    # permutace pouze na sloupcích
    elif symtype == "c":
        col = perms(n)

        for p in col:
            perm = get_perm(matrix, idpr, p)
            
            a = []
            b = []  
            for i in range(len(matrix)):
                a = a + matrix[i]
                b = b + perm[i]
                
            cls = get_clauses(a, b, kmax, aux)
            clauses += cls[0]
            aux = cls[1]

    # permutace na řadcích i sloupcích (nezávisle na sobě)
    elif symtype == "rc":
        row = perms(m)
        col = perms(n)
        row.append(idpr)
        col.append(idpc)
          
        for p in row:
            for q in col:
                if p == idpr and q == idpc:
                    continue
                perm = get_perm(matrix, p, q)

                a = []
                b = []  
                for i in range(len(matrix)):
                    a = a + matrix[i]
                    b = b + perm[i]
                    
                cls = get_clauses(a, b, kmax, aux)
                clauses += cls[0]
                aux = cls[1]

    else:
        pass

    return clauses

# %%
# načtení zadání ze souboru
cnf = CNF(from_file="inputqueens.cnf")
info = cnf.comments[0].split()

# získání klauzulí pro rozbití symetrií
s = time.time()
clauses = symmetry_clauses(get_matrix(int(info[1]),int(info[2])), info[3], neighbors, 1)
for clause in clauses:
  cnf.append(clause)
print("Symmetries: ", (time.time() - s) * 1e3, "ms")
print(" ")

# spuštění SAT solveru
s = time.time()
with Solver(bootstrap_with=cnf) as solver:
    print('formula is', f'{"S" if solver.solve() else "UNS"}ATisfiable')
    #print('and the model is:', solver.get_model())

print(" ")
print("SAT solver: ", (time.time() - s) * 1e3, "ms")

# uložení výsledku do souboru
cnf.to_file("output.cnf")

# %%



