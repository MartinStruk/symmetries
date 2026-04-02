#!/usr/bin/env python
# coding: utf-8

# In[33]:


from pysat.formula import CNF
from pysat.solvers import Solver
from itertools import permutations
from disjoint_set import DisjointSet
import time
import sys
import argparse
import random
from collections import defaultdict

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

# množina náhodných transpozic, která se porovná s neighbors
def randtrans(n):
    idp = list(range(n))
    seen = set()
    result = []

    while len(result) < n-1:
        i, j = sorted(random.sample(range(n), 2))
        if (i, j) not in seen:
            seen.add((i, j))
            seen.add((j, i))
            result.append(swap_positions(idp,i,j))

    return result

def nongen(n):
    idp = list(range(n))
    seen = set()
    result = []

    if n > 3:
        while len(result) < n-1:
            i, j = sorted(random.sample(range(n-1), 2))
            if (i, j) not in seen:
                seen.add((i, j))
                seen.add((j, i))
                result.append(swap_positions(idp,i,j))
    
    else:
        result = randtrans(n)
    
    return result

# dvouprvkový generátor grupy permutací
def gen2(n):
    result = [list((i+1) % n for i in range(n))]
    result.append(swap_positions(list(range(n)), 0, 1))
    return result

# rotace a reflexe
def dihedral_gen(n):
    size = n * n

    def index(i, j):
        return i * n + j

    rot = [0] * size
    refl = [0] * size

    for i in range(n):
        for j in range(n):
            old = index(i, j)

            # rotace 90° doprava
            new_i, new_j = j, n - 1 - i
            rot[old] = index(new_i, new_j)

            # reflexe podle svislé osy
            new_i, new_j = i, n - 1 - j
            refl[old] = index(new_i, new_j)

    return [rot, refl]

# sousední transpozice pro problém nalezení matice se řádky a sloupci se zadaným součtem
def sums_neighbors(values):
    groups = defaultdict(list)
    n = len(values)
    idp = list(range(n))

    # rozdělíme indexy podle hodnot
    for idx, val in enumerate(values):
        groups[val].append(idx)

    transpositions = []

    # pro každý blok generujeme sousední transpozice
    for indices in groups.values():
        if len(indices) > 1:
            for a, b in zip(indices, indices[1:]):
                transpositions.append(swap_positions(idp, a, b))

    return transpositions


# In[34]:


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
    n = len(a)
    OO = n+1
    II = n+2
    
    for i in range(n):
        if i >= kmax:
            break
        if a[i] == b[i]:
            continue
            
        clause = [-a[i],b[i]]
        # použité proměnné
        active = set([a[i], b[i]])

        # množiny rovnajících se proměnných 
        ds = DisjointSet()
        ds.union(OO, b[i])
        ds.union(II, a[i])

        # nalezení tříd ekvivalencí
        if i > 0:
            for k in range(i):
                if a[k] != b[k]:
                    ds.union(a[k], b[k])
                    active.add(a[k])
                    active.add(b[k])

        # pokud 0 = 1, konec
        cO = ds.find(OO)
        cI = ds.find(II)
        if cO == cI:
            continue

        canon = [ds.find(j) for j in active]
        active = list(active)

        # přidání klauzulí
        for j in range(len(active)):
            # proměnná je ve ekvivalentní s 0
            if canon[j] == cO:
                clause.append(active[j])

            # proměnná je ekvivalentní s 1
            elif canon[j] == cI:
                clause.append(-active[j])

            # proměnná je ekvivalentní jiné proměnné
            elif canon[j] != active[j]:
                try:
                    # pokud pro danou nerovnost již existuje proměnná navíc
                    clause.append(aux[(active[j], canon[j])])
                except:     
                    # pokud pro danou nerovnost ještě proměnná navíc neexistuje
                    clause.append(aux["curr"])                    
                    aux[(active[j], canon[j])] = aux["curr"]
                    aux[(canon[j], active[j])] = aux["curr"]
                    clauses.append([-aux["curr"],active[j],canon[j]])
                    clauses.append([-aux["curr"],-active[j],-canon[j]])
                    clauses.append([aux["curr"],-active[j],canon[j]])
                    clauses.append([aux["curr"],active[j],-canon[j]])
                    aux["curr"] = aux["curr"] + 1
    
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
    aux = {"curr" : m*n+3}

    # permutace pouze na řádcích
    if symtype == "r":
        row = perms(m)
        
        for p in row:
            perm = get_perm(matrix, p, idpc)
            
            a = []
            b = []  
            for i in range(m):
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
            for i in range(m):
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
                for i in range(m):
                    a = a + matrix[i]
                    b = b + perm[i]
                    
                cls = get_clauses(a, b, kmax, aux)
                clauses += cls[0]
                aux = cls[1]

    # rotace a reflexe
    elif symtype == "d":
        perm = perms(n)

        for p in perm:
            a = []
            b = []  
            for i in range(m):
                a = a + matrix[i]                
                for x in matrix[i]:
                    b.append(p[x-1]+1)
                    
            cls = get_clauses(a, b, kmax, aux)
            clauses += cls[0]
            aux = cls[1]

    # pro problém nalezení matice se řádky a sloupci se zadaným součtem 
    elif symtype[:4] == "sums":
        values = symtype[4:]
        rc = values.split('|')
        rsums = [int(x) for x in rc[0].split(',')]
        csums = [int(x) for x in rc[1].split(',')]

        row = perms(rsums)
        col = perms(csums)

        for p in row:
            for q in col:
                if p == idpr and q == idpc:
                    continue
                perm = get_perm(matrix, p, q)

                a = []
                b = []  
                for i in range(m):
                    a = a + matrix[i]
                    b = b + perm[i]
                    
                cls = get_clauses(a, b, kmax, aux)
                clauses += cls[0]
                aux = cls[1]

    # pro matice trojrozměrných problémů, které jsou přepsané do dvourozměrné matice
    elif symtype[:4] == "rc3d":
        row2d = int(symtype[4])
        val3d = m//row2d
        idpr2d = list(range(row2d))
        idpv = list(range(val3d))
        
        row = perms(row2d)
        row.append(idpr2d)
        col = perms(n)
        col.append(idpc)
        val = perms(val3d)
        val.append(idpv)
        for p in col:
            permc = get_perm(matrix, idpr, p)
            matrix3d = [permc[(i)*row2d:(i+1)*row2d] for i in range(val3d)]

            for q in row:
                permr = [get_perm(matrix3d[i],q,idpc) for i in range(val3d)]
                
                for r in val:
                    a = []
                    b = []  
                    for i in range(val3d):
                        for j in range(row2d):
                            a = a + matrix[i*row2d+j]
                            b = b + permr[r[i]][j]
                            
                cls = get_clauses(a, b, kmax, aux)
                clauses += cls[0]
                aux = cls[1]

                
    else:
        pass

    return clauses


# In[21]:


"""# načtení zadání ze souboru
cnf = CNF(from_file="inputgolf.cnf")
info = cnf.comments[0].split()

# získání klauzulí pro rozbití symetrií
s = time.time()
clauses = symmetry_clauses(get_matrix(int(info[1]),int(info[2])), info[3], neighbors, 2000)
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
print("SAT solver: ", (time.time() - s) * 1e3, "ms")"""


# In[22]:


def main():
    parser = argparse.ArgumentParser(description = "Možnosti pro vstupní argumenty:", formatter_class=argparse.RawTextHelpFormatter)

    parser.add_argument("problem", type=str, help="Problém, který dostaneme na vstupu. Možnosti: inputphp.cnf, inputqueens.cnf, inputrcsums.cnf, inputlatinsq.cnf, inputgolf.cnf")

    parser.add_argument("permutace", type=str, help="Množina permutací, která se použije pro generování klauzulí. Možnosti: all_perm, transpositions, neighbors, randtrans, nongen, gen2, dihedral_gen, sums_neighbors \nsums_neighbors je určeno speciálně pro inputrcsums.cnf")

    parser.add_argument("k", type=int, help="Hodnota k, která určuje maximální hloubku generování klauzulí pro jednotlivé vzory. Pro k menší nebo rovno 0 se nevygenerují žádné klauzule.")

    parser.add_argument("mc", type=bool, default=False, help="\"\" = False - zjišťujeme pouze, jestli je formule SAT nebo UNSAT \nTrue = hledáme počet všech řešení (model counting)")
    
    args = parser.parse_args()

    cnf = CNF(from_file=args.problem)
    info = cnf.comments[0].split()

    if args.mc:
        cnf.comments.append("c t pmc")
        cnf.comments.append("c p show " + " ".join(map(str, list(range(1, int(info[1])*int(info[2])+1)))) + " 0")
        
    perms = {"all_perm":all_perm, "transpositions":transpositions, "neighbors":neighbors, "randtrans":randtrans, "nongen":nongen, "gen2":gen2, "dihedral_gen":dihedral_gen, "sums_neighbors":sums_neighbors}
    
    clauses = symmetry_clauses(get_matrix(int(info[1]),int(info[2])), info[3], perms[args.permutace], args.k)
    for clause in clauses:
      cnf.append(clause)
   
    cnf.to_file("output.cnf")
    
if __name__ == "__main__":
    main()


# In[ ]:




