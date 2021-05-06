import itertools
from random import choice, seed
from time import time
from copy import deepcopy

class Proposicion:
    def __init__(self, name):
        self.name = name
        self.value = None

    def __str__(self):
        return f"{self.name} {self.value}"

    def __repr__(self):
        return self.__str__()


def dimacs(path):
    nprops = 0
    nclaus = 0
    props = []
    formula = []
    formula_index = 0
    with open(path) as file:
        data = file.readlines()
        for line in data:
            line_info = line.split()
            if len(line_info) == 0 or line_info[0] == 'c' or line_info[0] == '%' or line_info[0] == '0' or line_info[0] == '':
                continue
            elif line_info[0] == 'p' and line_info[1] == 'cnf':
                nprops = int(line_info[2])
                nclaus = int(line_info[3])
                for i in range(1, nprops + 1):
                    props.append(Proposicion(f"x{i}"))
                for i in range(nclaus):
                    formula.append([])
            else:
                formula_info = line_info[:len(line_info)-1]
                for lit in formula_info:
                    if lit[0] == '-':
                        formula[formula_index].append((1, props[int(lit[1:])-1]))
                    else:
                        formula[formula_index].append((0, props[int(lit[0:])-1]))
                formula_index += 1
    return formula, props

def eval(formula):
    all_claus_result = [0 for i in range(len(formula))]
    claus_index = 0
    for claus in formula:
        claus_result = None
        for lit in claus:
            if claus_result == None:
                if lit[0] == 1:
                    claus_result = 1-lit[1].value
                else:
                    claus_result = lit[1].value
            else:
                if lit[0] == 1:
                    claus_result = claus_result | 1-lit[1].value
                else:
                    claus_result = claus_result | lit[1].value
        all_claus_result[claus_index] = claus_result
        claus_index += 1
    result = all_claus_result[0]
    for i in range(1,len(all_claus_result)):
        result = result & all_claus_result[i]
    return result



def fuerzabruta(formula, props):
    nprops = len(props)
    combinations = list(itertools.product([0, 1], repeat=nprops))
    for combination in combinations:
        for i in range(nprops):
            props[i].value = combination[i]
        if eval(formula) == 1:
            return True
    return False


# Hay que redefinir
# def eval_clause(clause):
#     if clause[0][1].value == None:
#         return None
#     if clause[0][0] == 1:
#         result = 1 - clause[0][1].value
#     else:
#         result = clause[0][1].value
#     for i in range(1, len(clause)):
#         lit = clause[i]
#         if lit[1].value == None:
#             return None
#         if lit[0] == 1:
#             result = result | (1-lit[1].value)
#         else:
#             result = result | lit[1].value
#     return result



# def empty_clause(formula):
#     for clause in formula:
#         if eval_clause(clause) == 0:
#             return True
#     return False


def simplify(formula):

    remove_clauses = list()
    for clause in formula:
        for lit in clause:
            if lit[1].value != None:
                if lit[0] == 1:
                    if (1 - lit[1].value) == 1:
                        remove_clauses.append(clause)
                        break
                elif lit[0] == 0:
                    if lit[1].value == 1:
                        remove_clauses.append(clause)
                        break
    for clause in remove_clauses:
        formula.remove(clause)

    remove_lits = list()
    for clause in formula:
        remove_lits = [lit for lit in clause if ((lit[0] == 0 and lit[1].value == 0) or (lit[0] == 1 and lit[1].value == 1))]
        for lit in remove_lits:
            clause.remove(lit)
    return formula

def get_unit_clause(formula):
    for clause in formula:
        if len(clause) == 1:
            return clause[0]
    return None


def get_pure_lit(formula, props):
    for prop in props:
        sign = None
        same_sign = True
        for clause in formula:
            for lit in clause:
                if prop == lit[1]:
                    if sign == None:
                        sign = lit[0]
                    else:
                        if sign != lit[0]:
                            same_sign = False
        if same_sign and sign != None:
            return (sign, prop)
    return None


def empty_sentence(formula):
    if len(formula) == 0:
        return True
    else:
        return False

def empty_clause(formula):
    for clause in formula:
        if len(clause) == 0:
            return True
    return False

def mejorado(formula, props):

    if empty_clause(formula):
        return False
    if empty_sentence(formula):
        return True


    l1 = get_unit_clause(formula)
    if l1 != None:
        props.remove(l1[1])
        l1[1].value = (1 - l1[0])
        formula = simplify(formula)
        return mejorado(formula, props)
    


    l2 = get_pure_lit(formula, props)
    if l2 != None:
        props.remove(l2[1])
        l2[1].value = (1 - l2[0])
        formula = simplify(formula)
        return mejorado(formula, props)



    lit = props.pop(0)
    lit.value = 0
    props_copy = [(props[i], i) for i in range(len(props))]
    formula_copy = [clause.copy() for clause in formula]
    phi1 = simplify(formula)

    if mejorado(phi1, props):
        return True
    for prop, i in props_copy:
        if prop not in props:
            props.insert(i, prop)
        prop.value = None
    lit.value = 1
    formula = formula_copy


    phi2 = simplify(formula)
    if mejorado(phi2, props):
        return True
    else:
        lit.value = None
        return False



if __name__ == '__main__':
    for i in range(1, 21):
        time0 = time()
        print(f"data/20props satisfacibles/uf20-0{i}.cnf")
        formula, props = dimacs(f"data/20props satisfacibles/uf20-0{i}.cnf")
        print(mejorado(formula, props))
        print(time()- time0)

    # # # # # #50 insatisfacibles
    for i in range(1, 11):
        time0 = time()
        print(f"data/50props insatisfacibles/uuf50-0{i}.cnf")
        formula, props = dimacs(f"data/50props insatisfacibles/uuf50-0{i}.cnf")
        print(mejorado(formula, props))
        print(time() - time0)

    # # # #50 satisfacibles
    for i in range(1, 11):
        time0 = time()
        print(f"data/50props satisfacivles/uf50-0{i}.cnf")
        formula, props = dimacs(f"data/50props satisfacivles/uf50-0{i}.cnf")
        print(mejorado(formula, props))
        print(time()-time0)


