import timeit
import ply.lex as lex
import ply.yacc as yacc
import re
import copy
import time


class Node:
    def __init__(self, type, op=None, left=None, right=None):
        self.type = type
        self.left = left
        self.right = right
        self.op = op


class Tree:
    def __init__(self, root):
        self.root = root

    def preorder(self, tree):
        if tree is not None:
            print(tree.op, end="   ")
            self.preorder(tree.left)

            self.preorder(tree.right)

    def eliminateImplies(self, tree):
        if tree.left is None and tree.right is None:
            return tree
        if tree.op == '=>':
            tree.op = '|'
            newNode = Node("OPERATOR")
            newNode.op = '~'
            newNode.left = tree.left
            tree.left = newNode
        if tree.left is not None:
            self.eliminateImplies(tree.left)
        if tree.right is not None:
            self.eliminateImplies(tree.right)
        return tree

    def moveNegation(self, tree, parent):
        if tree.op == '~':
            if tree == self.root:
                if tree.left.op == '~':
                    self.root = tree.left.left
                    self.moveNegation(self.root, None)
                elif tree.left.op == '&' or tree.left.op == '|':
                    if tree.left.op == '&':
                        tree.op = '|'
                    elif tree.left.op == '|':
                        tree.op = '&'
                    x = tree.left.left
                    y = tree.left.right
                    newNegLeft = Node("OPERATOR", '~', tree.left.left)
                    tree.left = newNegLeft
                    newNegRight = Node("OPERATOR", '~', y)
                    tree.right = newNegRight
                    if tree.left is not None:
                        self.moveNegation(tree.left, tree)
                    if tree.right is not None:
                        self.moveNegation(tree.right, tree)
                elif tree.left.left is None:
                    tree.op = tree.op + tree.left.op
                    tree.type = "PREDICATE"
                    tree.left = None
                    return
            else:
                if tree.left.op == '~':
                    if parent.left is tree:
                        tree = tree.left.left
                        parent.left = tree
                        self.moveNegation(parent.left, parent)
                    elif parent.right is tree:
                        tree = tree.left.left
                        parent.right = tree
                        self.moveNegation(parent.right, parent)
                elif tree.left.op == '&' or tree.left.op == '|':
                    if tree.left.op == '&':
                        tree.op = '|'
                    elif tree.left.op == '|':
                        tree.op = '&'
                    x = tree.left.left
                    y = tree.left.right
                    newNegLeft = Node("OPERATOR", '~', tree.left.left)
                    tree.left = newNegLeft
                    newNegRight = Node("OPERATOR", '~', y)
                    tree.right = newNegRight
                    if tree.left is not None:
                        self.moveNegation(tree.left, tree)
                    if tree.right is not None:
                        self.moveNegation(tree.right, tree)
                elif tree.left.left is None:
                    tree.op = tree.op + tree.left.op
                    tree.type = "PREDICATE"
                    tree.left = None
                    return

        elif tree.op == '|':
            self.moveNegation(tree.left, tree)
            self.moveNegation(tree.right, tree)
        elif tree.op == '&':
            self.moveNegation(tree.left, tree)
            self.moveNegation(tree.right, tree)
        elif tree.left is None and tree.right is None:
            return
        return tree

    def distribute(self, tree):
        if tree.left is None and tree.right is None:
            return tree
        if tree.op == '|':
            if tree.left.op == '&':
                tree.op = '&'
                leftleft = tree.left.left
                leftright = tree.left.right
                right = tree.right
                leftTree = Node("OPERATOR", '|', leftleft, right)
                tree.left = leftTree
                rightTree = Node("OPERATOR", '|', leftright, right)
                tree.right = rightTree
                self.distribute(tree.left)
                self.distribute(tree.right)
            elif tree.right.op == '&':
                tree.op = '&'
                leftleft = tree.right.left
                leftright = tree.right.right
                left = tree.left
                leftTree = Node("OPERATOR", '|', left, leftleft)
                tree.left = leftTree
                rightTree = Node("OPERATOR", '|', left, leftright)
                tree.right = rightTree
                self.distribute(tree.left)
                self.distribute(tree.right)
            elif tree.left.op is not None or tree.right.op is not None:
                if tree.left.op is not None:
                    self.distribute(tree.left)
                if tree.right.op is not None:
                    self.distribute(tree.right)
        else:
            self.distribute(tree.left)
            self.distribute(tree.right)
        return tree

    def distribute_loop(self, tree):
        if tree is None:
            return True
        if tree.op == '|':
            if tree.left == '&' or tree.right.op == '&':
                return False
            else:
                return True
        else:
            return self.distribute_loop(tree.left) and self.distribute_loop(tree.right)

    def parse_tree(self, tree):

        if tree is None:
            return []
        elif tree.type == "PREDICATE":
            return [tree.op]
        elif tree.op == '&':
            result = []
            l = self.parse_tree(tree.left)
            r = self.parse_tree(tree.right)

            if isinstance(l[0], list):
                result += l
            else:
                result += [l]

            if isinstance(r[0], list):
                result += r
            else:
                result += [r]

            return result

        elif tree.op == '|':
            return self.parse_tree(tree.left) + self.parse_tree(tree.right)
        elif tree.op == '~':
            return ['~'] + self.parse_tree(tree.left)


class PredicateArgs:
    def __init__(self, expr):
        self.expr = expr
        self.pname = ''
        self.args = []
        self.neg = False
        self.arglist = {}

    def __str__(self):
        return "\nExp: " + self.expr + "\nName: " + self.pname + "\narglist: " + str(self.arglist) + "\n"

    def sepexpr(self):
        separate = re.search('[~]?([A-Z][A-Za-z]*)\(([A-Za-z,0-9]+)\)', self.expr)
        if self.expr[0] == '~':
            self.neg = True
        else:
            self.neg = False
        self.pname = separate.group(1)
        b = separate.group(2)
        a = b.split(',')
        for i in a:
            self.args.append(i)
            if i[0].isupper():
                self.arglist[i] = 'Constant'
            else:
                self.arglist[i] = 'Variable'


def unify(x, y, theta):
    if theta is None:
        return None
    elif x == y:
        return theta
    elif is_variable(x):
        return unify_var(x, y, theta)
    elif is_variable(y):
        return unify_var(y, x, theta)
    elif isinstance(x, PredicateArgs) and isinstance(y, PredicateArgs):
        return unify(x.args, y.args, unify(x.pname, y.pname, theta))
    elif isinstance(x, list) and isinstance(y, list):
        return unify(x[1:], y[1:], unify(x[0], y[0], theta))
    else:
        return None


def unify_var(var, x, theta):
    if var in theta:
        return unify(theta[var], x, theta)
    # elif self.occur_check(var, x):
    #	return None
    else:
        theta2 = theta.copy()
        theta2[var] = x
        return theta2


# check if var occurs in theta
def occur_check(var, theta):
    if var == theta:
        return True
    elif isinstance(theta, PredicateArgs):
        return var == theta.name or occur_check(var, theta.args)
    elif isinstance(theta, list):
        if var in list:
            return True
    return False


def is_variable(s):
    return isinstance(s, str) and s.islower()


def compare(i, j):
    iseparate = re.search('[~]?([A-Z][A-Za-z]*)\(([A-Za-z,0-9]+)\)', i)
    jseparate = re.search('[~]?([A-Z][A-Za-z]*)\(([A-Za-z,0-9]+)\)', j)
    ipname = iseparate.group(1)
    if i[0] == '~':
        ineg = True
        ipname = '~' + ipname
    else:
        ineg = False

    jpname = jseparate.group(1)
    if j[0] == '~':
        jneg = True
        jpname = '~' + jpname
    else:
        jneg = False

    if ipname == '~' + jpname or '~' + ipname == jpname:
        ithobject = PredicateArgs(i)
        ithobject.sepexpr()
        jthobject = PredicateArgs(j)
        jthobject.sepexpr()
        unifiedlist = unify(ithobject, jthobject, {})
        return unifiedlist
    else:
        return None


def newclause(c1, c2, i, j, unifiedlist):
    newclauses = [[]]
    for k in c1:
        if k is not i:
            argindex = k.find("(")
            pname = k[:argindex]
            arg = k[argindex + 1:-1]
            arglist = arg.split(",")
            newarglist = []
            for key, value in unifiedlist.items():
                for n, item in enumerate(arglist):
                    if key == item:
                        arglist[n] = value

            argliststr = ','.join(map(str, arglist))
            finalstr = pname + '(' + argliststr + ')'
            for element in newclauses:
                if finalstr not in element:
                    element.append(finalstr)
    for l in c2:
        if l is not j:
            argindex = l.find("(")
            pname = l[:argindex]
            arg = l[argindex + 1:-1]
            arglist = arg.split(",")
            newarglist = []
            for key, value in unifiedlist.items():
                for n, item in enumerate(arglist):
                    if key == item:
                        arglist[n] = value

            argliststr = ','.join(map(str, arglist))
            finalstr = pname + '(' + argliststr + ')'
            for m in newclauses:
                if finalstr not in m:
                    m.append(finalstr)
    for n in newclauses:
        if not n:
            return False
        else:
            return newclauses


# ['~F(x)', 'G(x)']  ['~G(x)', 'F(x)']
def resolve(c1, c2):
    clause = [[]]
    completeclause = [[]]
    for i in c1:
        for j in c2:
            unifiedlist = compare(i, j)
            if unifiedlist is not None:
                if any(unifiedlist) is True:
                    clause = newclause(c1, c2, i, j, unifiedlist)
                    if clause == False:
                        return False
                    completeclause.append(clause)
                else:
                    if len(c1) is 1 and len(c2) is 1:
                        # resolve output of A(x)|P(x) and ~P(x)|C(x) ???? have returned true , should keep this or discard ?
                        return False
                    else:
                        clause = newclause(c1, c2, i, j, unifiedlist)
                        completeclause.append(clause)
    if len(completeclause) > 1:
        completeclause.pop(0)
        return completeclause
    else:
        return completeclause


def resolution(KB):
    #subset = set()
    timeout = time.time() + 15 * 60
    while True:
        subset = set()
        KBtuple = [tuple(x) for x in KB]
        KBset = set(KBtuple)
        n = len(KB)
        pairs = [(KB[i], KB[j]) for i in range(n) for j in range(i + 1, n)]
        for (i, j) in pairs:
            resolved = resolve(i, j)
            # print("Resolved = ", resolved, "\nc1 = ", i, "\nc2 = ",j, "\n")
            if resolved == False:
                return True
            for p in resolved:
                if not p:
                    pass
                    # print("empty nested list")
                else:
                    #print("Resolved = ", resolved, "\nc1 = ", i, "\nc2 = ",j, "\n")
                    resolvedtuple = [tuple(y) for y in p]
                    resolvedset = set(resolvedtuple)
                    subset.update(resolvedset)
        if subset.issubset(KBset):
            return False
        if len(subset) > 25000:
            return False

        for k in subset:
            if k not in KBset:
                ij = list(k)
                KB.append(ij)
                # KB.insert(0, ij)
        if time.time() > timeout:
            return False


def changevariable(expr, index):
    separate = re.search('[~]?([A-Z][A-Za-z]*)\(([A-Za-z,]+)\)', expr)
    if expr[0] == '~':
        neg = True
    else:
        neg = False
    pname = separate.group(1)
    b = separate.group(2)
    a = b.split(',')
    c = []
    for i in a:
        if len(i) == 1 and i.islower():
            i = i + str(index + 1)
            c.append(i)
        else:
            c.append(i)
    argliststr = ','.join(map(str, c))
    if neg is True:
        finalst = '~' + pname + '(' + argliststr + ')'
    else:
        finalst = pname + '(' + argliststr + ')'
    return finalst


def standardize(statement, index):
    lists = any(isinstance(i, list) for i in statement)
    if lists is True:
        for ind, k in enumerate(statement):
            for inde, l in enumerate(k):
                changedvariable = changevariable(l, index)
                statement[ind][inde] = changedvariable

    else:
        updatedstatement = []
        for inex, j in enumerate(statement):
            changedvariable = changevariable(j, index)
            statement[inex] = changedvariable
    return statement



def checkifqueryinKB(query, KB):
    presentornot = False
    for a in KB:
        for b in a:
            iiseparate = re.search('[~]?([A-Z][A-Za-z]*)\(([A-Za-z,0-9]+)\)', query)
            jjseparate = re.search('[~]?([A-Z][A-Za-z]*)\(([A-Za-z,0-9]+)\)', b)
            iipname = iiseparate.group(1)
            if query[0] == '~':
                iipname = '~' + iipname
            jjpname = jjseparate.group(1)
            if b[0] == '~':
                jjpname = '~' + jjpname
            if iipname == jjpname:
                return True
    return presentornot



tokens = [
    'LPAREN',
    'RPAREN',
    'PREDICATE',
    'AND',
    'OR',
    'IMPLIES',
    'NEGATION'
]

t_PREDICATE = r'[A-Z][A-Za-z]*\(([A-Za-z,]+)\)'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_AND = r'\&'
t_OR = r'\|'
t_IMPLIES = r'\=>'
t_NEGATION = r'\~'

t_ignore = r' '


def t_error(t):
    print("Illegeal characters")
    t.lexer.skip(1)


lexer = lex.lex()


def p_expression_single(p):
    '''
    expression : PREDICATE
    '''
    p[0] = Node("PREDICATE", p[1])
    # print( p[0])


def p_expression_negation(p):
    '''
    expression : NEGATION expression
    '''
    p[0] = Node("OPERATOR", p[1], p[2])
    # print(p[0])


def p_expression_operation(p):
    '''
    expression : expression IMPLIES expression
               | expression AND expression
               | expression OR expression
    '''
    p[0] = Node("OPERATOR", p[2], p[1], p[3])


def p_expression_brackets(p):
    '''
    expression : LPAREN expression RPAREN
    '''
    p[0] = p[2]


def p_error(p):
    print("Syntax error in input!")


parser = yacc.yacc()

with open('input.txt', 'r') as f:
    file = f.read()
    mainlist = file.splitlines()

start = timeit.default_timer()
numberofquery = mainlist[0]
querylist = []
for i in mainlist[1:1 + int(numberofquery)]:
    j = i.replace(" ", "")
    querylist.append(j)

m = 1 + int(numberofquery)
numberofsentence = mainlist[m]
Sentenceslist = []
for i in mainlist[m + 1: m + 2 + int(numberofsentence)]:
    Sentenceslist.append(i.replace(" ", ""))

KB = []
for index, s in enumerate(Sentenceslist):
    root = parser.parse(s, lexer=lexer)
    treeObj = Tree(root)

    # print("\n--Below is Intial Expression-------\n")
    # treeObj.preorder(root)
    # print('\n')
    treeObj.eliminateImplies(treeObj.root)
    # print("\n--Below is Result after eliminating implication-------\n")
    # treeObj.preorder(treeObj.root)
    # print('\n')
    # print("\n--Below is Result after moving negation inwards--------\n")
    treeObj.moveNegation(treeObj.root, None)
    #treeObj.preorder(treeObj.root)
    # print('\n')
    # print("\n--Below is Result after Distribution--------\n")
    while (True):
        rnode = treeObj.distribute(treeObj.root)
        if treeObj.root is rnode:
            if treeObj.distribute_loop(treeObj.root):
                break
        treeObj.root = rnode
    #treeObj.preorder(treeObj.root)
    k = treeObj.parse_tree(treeObj.root)
    # print("Look for this", k)
    #print("All the statement before standar\n", k)
    updatedstatement = []
    updatedstatement = standardize(k, index)
    # print("\n\nAll the statement after standar\n", k)
    asd = any(isinstance(i, list) for i in updatedstatement)
    if asd is True:
        for i in updatedstatement:
            KB.append(i)
    else:
        KB.append(updatedstatement)

output = []
for p in querylist:
    parseTree = []
    # KB = []
    if p[0] == '~':
        negquery = p[1:]
    else:
        negquery = '~' + p
    # print("List of sentences in KB before adding query\n", KB)
    querypresent = checkifqueryinKB(p, KB)
    if querypresent is True:
        KB.insert(0, [negquery])
        KBcopy = copy.deepcopy(KB)
        value = resolution(KBcopy)
        KB.remove([negquery])
    else:
        value = False
    # print("Final answer is", value)
    output.append(value)


with open('output.txt', 'w') as fwrite:
    for i in output:
        if i == True:
            fwrite.write("TRUE" + '\n')
        else:
            fwrite.write("FALSE" + '\n')

stop = timeit.default_timer()

# print(stop - start)


