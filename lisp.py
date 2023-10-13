#
#   lisp.py
#
#   Copyright © 2021 Chris Meyers and Fred Obermann
#   https://www.openbookproject.net/py4fun/lisp/lisp.html
#
#   2023, Modified by Alexandre Dumont <adumont@gmail.com>
#   Ported to HP Prime & More modifications

import sys
import math

if sys.platform == 'HP Prime':
    is_prime = True
    import hpprime
    import graphic
    import urandom

    graphic.clear_screen(0xffffff)
    hpprime.eval("print")

    def debug(func): # fake decorator for the Prime
        return func

else:
    is_prime = False

    sys.setrecursionlimit(10**4)

    import functools

    debug_indent = 0
    def debug(func):
        """Print the function signature and return value"""
        @functools.wraps(func)
        def wrapper_debug(*args, **kwargs):
            global debug_indent
            args_repr = [repr(a) for a in args]                      # 1
            kwargs_repr = [f"{k}={v!r}" for k, v in kwargs.items()]  # 2
            signature = ", ".join(args_repr + kwargs_repr)           # 3
            print(f"{'  '*debug_indent}Calling {func.__name__}({signature})")
            debug_indent += 1
            value = func(*args, **kwargs)
            debug_indent -= 1
            print(f"{'  '*debug_indent}{func.__name__}({signature}) returned {value!r}")           # 4
            return value
        return wrapper_debug


print("LISP for HP Prime v0.0 - @adumont")

debug_flag = False          # show trace of evaluations if true
Alist = []             # Hold the global defs

# Bootstrap LISP Code
# https://shaunlebron.github.io/parinfer/ --> Parinfer's "Indent Mode" rearranges parens when you change indentation
inlin = """
(defun fact (x)
  (cond
    ( (eq x 0) 1)
    ( t        (* x (fact (- x 1))))))

(defun member ( X L)
  (cond
    ( (eq L () )      ())
    ( (eq X (car L )) L)
    ( t               (member X (cdr L)))))

(defun reverse (L)
  (cond
    ( (not L) ())
    ( t (append (reverse (cdr L)) (car L)))))
"""

# @debug
def putSexp(s):
    # return string form of an S expression
    if type(s) == type([]):
        if len(s) and s[0] == 'quote':
            return "'" + putSexp(s[1])
        else:
            return '(' + ' '.join(map(putSexp,s)) + ')'
    else:
        return str(s)

# @debug
def getSexp():
    # get an S expression from the user
    # return and discard the next S expression,
    #   along with any nested ones in input
    a = getToken()

    if   a == "'":
        return ['quote', getSexp()]
    elif a != '(':
        return a

    a = []

    while 1:
        b = getSexp()
        if b == ')':
            return a
        a.append(b)

def getToken():
    # return and discard the next symbol,
    #   number or special character in input
    while nextChar() <= ' ': getChar()  # skip whitespace
    a = getChar()
    if a in ['(',')',"'"] : return a
    while nextChar() > ' ' and nextChar() not in ['(',')'] :
        a = a + getChar()
    try    : return float(a)   # if a number, make it a float
    except : return a          # otherwise a string with the symbol name

def getFile(fname):
    output = []
    lines = open(fname).readlines()
    for line in lines :
        line = line.rstrip()
        if line[0:1] == '@' :
            output.append(getFile(line[1:]))
        else :
            output.append(line)
    return '\n'.join(output)

def nextChar():
    # return (but don't discard) the next character in the input stream
    #   get more from the user if needed
    global inlin, inputter
    if inlin == "" :
        inlin = input("LISP>")
        # if inlin == "" : sys.exit()
        inlin=inlin + " "
        if inlin[0] == '@' :
            inlin = getFile(inlin[1:])

    return inlin[0:1]

def getChar():
    # return and discard the next character in the input stream
    global inlin
    c = nextChar()
    inlin = inlin[1:]
    return c

def isSymbol(x): return type(x) == type('')
def isNumber(x): return type(x) == type(0.0)

# @debug
def bind(names,values,alist):
    """push symbols in x with respective values in y onto the alist"""
    if not names:
        return alist
    else:
        return [[names[0],values[0]]] + bind(names[1:],values[1:],alist)

#@debug
def resolve(symbol, env):
    "look up x on the alist and return its value"

    for name,value in env:
        if name == symbol:
            return value

    return []    # nil

def _diff(args):
    if len(args) == 1:
        return -args[0]
    else:
        return args[0]-sum(args[1:])

def _prod(args):
    tmp=1.0
    for n in args:
        tmp = tmp * n
    return tmp

def _div(args):
    if len(args) == 1:
        return 1.0/args[0]
    else:
        tmp=args[0]
        for n in args[1:]:
            tmp = tmp / n
        return tmp

# @debug
def update_global(name, value, alist):
    "Add/Update global variable to alist"

    if len(alist) > 0:
        for i in range(len(alist)-1, -1, -1):
            if alist[i][0] == name:
                alist[i][1] = value
                return alist

    return [[name,value]] + alist

# @debug
def _setq(exp, alist, ret):
    "Processes the list two by two, returns the last"
    global Alist

    if len(exp)<2: return ret
    else:
        tmp=eval(exp[1], alist)
        alist = Alist = update_global( exp[0], tmp, alist )
        return _setq(exp[2:], alist, tmp)

def _print(args):
    for a in args:
        print(a, end=" ")
    return a

# @debug
def apply(fn,args,alist):
    "apply a function fn to its arguments in args"
    if debug_flag :
        print("--Apply-- %s  Args=%s" % (putSexp(fn),putSexp(args)))
        printAlist(alist)

    if isSymbol(fn):   # name of a function
        if   fn == 'atom' : return [[],'t'][type(args[0]) != type([])]
        elif fn == 'car'  : return args[0][0]   # first element of 1st arg
        elif fn == 'cdr'  : return args[0][1:]  # tail of 1st arg
        elif fn == '+'    : return  sum(args)
        elif fn == '-'    : return _diff(args)
        elif fn == '*'    : return _prod(args)
        elif fn == '/'    : return _div(args)
        elif fn == 'eq'   : return [[],'t'][args[0] == args[1]]
        elif fn == '<'    : return [[],'t'][args[0] <  args[1]]
        elif fn == '<='   : return [[],'t'][args[0] <= args[1]]
        elif fn == '>'    : return [[],'t'][args[0] >  args[1]]
        elif fn == '>='   : return [[],'t'][args[0] >= args[1]]
        elif fn == 'not'  : return [[],'t'][args[0] == []]
        elif fn == 'eval' : return eval(args[0], alist)
        elif fn == 'print': return _print(args)
        elif fn == 'cons' :
            if type(args[1]) != type([]):
                args[1] = [args[1]]
            return [args[0]] + args[1]
        elif fn == 'cos'  : return math.cos(args[0])
        elif fn == 'sin'  : return math.sin(args[0])
        elif fn == 'tan'  : return math.tan(args[0])
        else:
            return (apply(eval(fn,alist),args,alist))
    elif fn[0] == 'lambda' : # a function definition
        # EVAL ALL forms in the lambda definition
        tmp_alist = bind( names=fn[1], values=args, alist=alist )
        for i in range(2,len(fn)):  # this loop isn't Lispy... there must be a recursive way?
            tmp = eval(fn[i], tmp_alist)
        return tmp
        # tmp_alist = alist
        # for i in range(2,len(fn)):  # this loop isn't Lispy... there must be a recursive way?
        #     tmp_alist = pairlis(fn[1],args,tmp_alist)
        #     tmp = eval(fn[i], pairlis(fn[1],args,tmp_alist))
        # return tmp
    else:
        scream("Can't apply %s" % fn)

# @debug
def eval(exp, alist):
    "evaluate an S expression using the alist"
    global Alist
    if debug_flag : print("--Eval--- %s" %  putSexp(exp)); printAlist(alist)
    if   exp == 't'     : return 't'      # true evaluates to itself
    elif exp == 'nil'   : return []       # symbol nil same as a null list
    elif exp == []      : return []
    elif exp == 'alist' : return Alist    # special command to examine alist
    elif isNumber(exp)  : return exp      # numbers eval to themselves
    elif isSymbol(exp)  : return resolve(symbol=exp,env=alist)  # look up variables
    else :               # check for special forms
        if exp[0] == 'quote':
            return exp[1]
        if exp[0] == 'list':               # (list 'A 'B '(C)') => (A B (C))
            return evlis(exp[1:], alist)
        if exp[0] == 'append':             # (append '(a b c) '(d e f) '() '(g)) =>  (A B C D E F G)
            tmp = []
            for l in evlis(exp[1:], alist):
                tmp += l
            return tmp
        elif exp[0] == 'setq':
            return _setq(exp[1:], alist, [])
        elif exp[0] == 'set':
            return _setq( evlis(exp[1:], alist) , alist, [])
        elif exp[0] == 'def' :
            # user define functions
            # LISP> (def test (lambda (a b) (+ a b 1 )))
            alist = Alist = bind( names=[exp[1]] , values=[exp[2]] , alist=alist)
            return exp[1] # return function name
        elif exp[0] == 'defun' :
            # user define functions
            # LISP> (defun test (a b) (+ a b 1 ))
            alist = Alist = bind( names=[exp[1]] , values=[ ['lambda'] + exp[2:]] , alist=alist)
            return exp[1] # return function name
        elif exp[0] == 'cond':
            return evcon(exp[1:], alist)
        else:
            x = evlis(exp[1:], alist)
            return apply( exp[0], x , alist )

# @debug
def evcon(c, alist):
    "evaluate cond. Note just the pairs passed in c"
    if   len(c) == 0           : return []
    elif eval (c[0][0], alist) : return eval (c[0][1],alist)
    else                       : return evcon(c[1:],  alist)

# @debug
def evlis(list, alist):
    "evaluate all elements in a list, returning list of the values"
    if not list:
        return []
    else:
        return [ eval(list[0], alist) ] + evlis( list[1:], alist )

def printAlist(alist):
    print("Alist")
    for name,sexp in alist :
        sexp = putSexp(sexp)
        output = "(%s %s)" % (name,sexp)
        print(output)

def scream(mesg):
    print("Exiting: %s" % mesg)
    # sys.exit(1)

def main():
    "get S expressions and evaluate them. Print the results"
    global Alist, debug_flag
    while True :
        s = getSexp()
        if   s == 'alist' : printAlist(Alist)
        elif s == 'exit' or s == 'quit'  : quit()
        elif s == 'debug' : debug_flag = not debug_flag
        else :
            if is_prime:
                print(putSexp(s))
            try    : print(putSexp(eval(s ,Alist)))
            except :
                scream("cant eval %s " % s)
                raise

if __name__ == "__main__" : main()