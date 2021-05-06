import itertools
from time import time


class Proposicion:
    """
    Clase que representa una propsición
    self.name: Nombre de la proposición
    self.value: Valor que toma actualmente (1 para verdadero, 0 para falso y
    None si no está asignada)
    """

    def __init__(self, name):
        self.name = name
        self.value = None

    def __str__(self):
        return f"{self.name} {self.value}"

    def __repr__(self):
        return self.__str__()


def dimacs(path):
    """
    Función dimacs que recibe un PATH a un archivo .cnf que represente una
    fórmula en CNF. Procesa el archivo y retorna una tupla, donde el primer
    elemento es una lista de lista, donde cada sublista representa a las
    cláusulas y la lista grande la disjunción de cláusulas. La segunda lista
    representa las proposiciones, enumeradas de forma ordenada, de la fórmula.
    """
    nprops = 0
    nclaus = 0
    props = []
    formula = []
    formula_index = 0
    with open(path) as file:
        data = file.readlines()
        for line in data:
            line_info = line.split()
            if (
                len(line_info) == 0
                or line_info[0] == "c"
                or line_info[0] == "%"
                or line_info[0] == "0"
                or line_info[0] == ""
            ):
                continue
            elif line_info[0] == "p" and line_info[1] == "cnf":
                nprops = int(line_info[2])
                nclaus = int(line_info[3])
                for i in range(1, nprops + 1):
                    props.append(Proposicion(f"x{i}"))
                for i in range(nclaus):
                    formula.append([])
            else:
                formula_info = line_info[: len(line_info) - 1]
                for lit in formula_info:
                    if lit[0] == "-":
                        formula[formula_index].append(
                            (1, props[int(lit[1:]) - 1])
                        )
                    else:
                        formula[formula_index].append(
                            (0, props[int(lit[0:]) - 1])
                        )
                formula_index += 1
    return formula, props


def eval(formula):
    """
    Evalúa una fórmula, con todas sus proposiciones con valores
    asignados, retorna 1 o 0.
    """
    all_claus_result = [0 for i in range(len(formula))]
    claus_index = 0
    for claus in formula:
        claus_result = None
        for lit in claus:
            if claus_result is None:
                if lit[0] == 1:
                    claus_result = 1 - lit[1].value
                else:
                    claus_result = lit[1].value
            else:
                if lit[0] == 1:
                    claus_result = claus_result | 1 - lit[1].value
                else:
                    claus_result = claus_result | lit[1].value
        all_claus_result[claus_index] = claus_result
        claus_index += 1
    result = all_claus_result[0]
    for i in range(1, len(all_claus_result)):
        result = result & all_claus_result[i]
    return result


def fuerzabruta(formula, props):
    """
    Algoritmo de fuerza bruta para el problema de SAT
    que retorna True si es que la fórmula es
    satisfacible y False en caso contrario.
    """
    nprops = len(props)
    combinations = list(itertools.product([0, 1], repeat=nprops))
    for combination in combinations:
        for i in range(nprops):
            props[i].value = combination[i]
        if eval(formula) == 1:
            return True
    return False


def simplify(formula):
    """
    Simplifica una fórmula según los valores de proposiciones
    que estén asignados en ella.
    """
    remove_clauses = list()
    for clause in formula:
        for lit in clause:
            if lit[1].value is not None:
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
        remove_lits = [
            lit
            for lit in clause
            if (
                (lit[0] == 0 and lit[1].value == 0)
                or (lit[0] == 1 and lit[1].value == 1)
            )
        ]
        for lit in remove_lits:
            clause.remove(lit)
    return formula


def get_unit_clause(formula):
    """
    Obtiene la literal de una cláusula unitaria de la fórmula (si es que hay).
    """
    for clause in formula:
        if len(clause) == 1:
            return clause[0]
    return None


def get_pure_lit(formula, props):
    """
    Obtiene una literal pura de la fórmula (si es que hay).
    """
    for prop in props:
        sign = None
        same_sign = True
        for clause in formula:
            for lit in clause:
                if prop == lit[1]:
                    if sign is None:
                        sign = lit[0]
                    else:
                        if sign != lit[0]:
                            same_sign = False
        if same_sign and sign is not None:
            return (sign, prop)
    return None


def empty_sentence(formula):
    """
    Retorna True si es que no quedan cláusulas en la fórmula (lista vacía) y
    False en caso contrario.
    """
    if len(formula) == 0:
        return True
    else:
        return False


def empty_clause(formula):
    """
    Retorna True si es que hay una cláusula vacía en la fórmula (sublista vacía)
    y False en caso contrario.
    """
    for clause in formula:
        if len(clause) == 0:
            return True
    return False


def mejorado(formula, props):
    """
    Algoritmo DPLL con heurísticas
    """

    # Casos base

    # Si hay cláusulas vacías, entonces hay una cláusula simplificada a Falso,
    # por lo que retornamos False
    if empty_clause(formula):
        return False

    # Si la fórmula es vacía, entonces todas las cláusulas se simplificaron a
    # Verdadero, por lo que retornamos True
    if empty_sentence(formula):
        return True

    # Si hay una cláusula unitaria, sabemos que ese valor deberá ser 1 (o ~0)
    # para que se haga True
    l1 = get_unit_clause(formula)
    if l1 is not None:
        props.remove(l1[1])
        l1[1].value = 1 - l1[0]
        formula = simplify(formula)
        return mejorado(formula, props)

    # Si hay una literal pura, ese valor deberá ser 1 (o ~0)
    # para que inmediatamente se haga True todas las cláusulas en que está
    #  presente
    l2 = get_pure_lit(formula, props)
    if l2 is not None:
        props.remove(l2[1])
        l2[1].value = 1 - l2[0]
        formula = simplify(formula)
        return mejorado(formula, props)

    # Flujo del backtracking, revisamos una variable arbitraria y revisamos si
    # funciona asignar a True o False.
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


if __name__ == "__main__":
    PATH_TO_SAT_50 = "data/50props satisfacivles/"
    PATH_TO_SAT_20 = "data/20props satisfacibles/"
    PATH_TO_UNSAT_50 = "data/50props insatisfacibles/"

    print("Fuerza bruta:\n")
    for i in range(1, 21):
        time0 = time()
        print(f"SAT 20 - {i}")
        formula, props = dimacs(f"{PATH_TO_SAT_20}uf20-0{i}.cnf")
        fuerzabruta(formula, props)  # Agregar print para ver que es correcto
        print(time() - time0)
        print("\n")

    print("DPLL:\n")
    for i in range(1, 21):
        time0 = time()
        print(f"SAT 20 - {i}")
        formula, props = dimacs(f"{PATH_TO_SAT_20}uf20-0{i}.cnf")
        mejorado(formula, props)  # Agregar print para ver que es correcto
        print(time() - time0)
    print("\n")

    # # # # # #50 insatisfacibles
    for i in range(1, 11):
        time0 = time()
        print(f"UNSAT 50 -{i}")
        formula, props = dimacs(f"{PATH_TO_UNSAT_50}uuf50-0{i}.cnf")
        mejorado(formula, props)  # Agregar print para ver que es correcto
        print(time() - time0)
    print("\n")

    # # # #50 satisfacibles
    for i in range(1, 11):
        time0 = time()
        print(f"50 SAT {i}")
        formula, props = dimacs(f"{PATH_TO_SAT_50}uf50-0{i}.cnf")
        mejorado(formula, props)  # Agregar print para ver que es correcto
        print(time() - time0)
    print("\n")
