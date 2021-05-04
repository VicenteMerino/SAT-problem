import itertools

class Proposicion:
    def __init__(self, name):
        self.name = name
        self.value = None

    def __str__(self):
        return self.name

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
                    claus_result = ~lit[1].value
                else:
                    claus_result = lit[1].value
            else:
                if lit[0] == 1:
                    claus_result = claus_result | ~lit[1].value
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


def mejorado(formula):
    pass

if __name__ == '__main__':
    formula, props = dimacs("data/20props satisfacibles/uf20-05.cnf")
    # for claus in formula:
    #     print(claus)
    result = fuerzabruta(formula, props)
    print(result)
