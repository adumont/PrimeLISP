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

    import functools

    def debug(func):
        """Print the function signature and return value"""
        @functools.wraps(func)
        def wrapper_debug(*args, **kwargs):
            args_repr = [repr(a) for a in args]                      # 1
            kwargs_repr = [f"{k}={v!r}" for k, v in kwargs.items()]  # 2
            signature = ", ".join(args_repr + kwargs_repr)           # 3
            print(f"Calling {func.__name__}({signature})")
            value = func(*args, **kwargs)
            print(f"{func.__name__}({signature}) returned {value!r}")           # 4
            return value
        return wrapper_debug


print("LISP for HP Prime v0.0 - @adumont")

debug_flag = False          # show trace of evaluations if true
Alist = []             # Hold the global defs

inlin = ""

# @debug
def putSexp(s):
    # return string form of an S expression
    if type(s) == type([]) :
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

def getToken() :
    # return and discard the next symbol,
    #   number or special character in input
    while nextChar() <= ' ': getChar()  # skip whitespace
    a = getChar()
    if a in ['(',')',"'"] : return a
    while nextChar() > ' ' and nextChar() not in ['(',')'] :
        a = a + getChar()
    try    : return float(a)   # if a number, make it a float
    except : return a          # otherwise a string with the symbol name

def getFile(fname) :
    output = []
    lines = open(fname).readlines()
    for line in lines :
        line = line.rstrip()
        if line[0:1] == '@' :
            output.append(getFile(line[1:]))
        else :
            output.append(line)
    return '\n'.join(output)

def nextChar() :
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

def getChar() :
    # return and discard the next character in the input stream
    global inlin
    c = nextChar()
    inlin = inlin[1:]
    return c

def isSymbol(x) : return type(x) == type('')
def isNumber(x) : return type(x) == type(0.0)

# @debug
def pairlis(x,y,alist) :
    """push symbols in x with respective values in y onto the alist"""
    if not x:
        return alist
    else:
        return [[x[0],y[0]]] + pairlis(x[1:],y[1:],alist)

def assoc (x, alist) :
    "look up x on the alist and return its value"
    if   not alist        : return []    # nil
    elif alist[0][0] == x : return alist[0][1]
    else                  : return assoc(x,alist[1:])

def _diff(args):
    if len(args) == 1:
        return -args[0]
    else:
        return args[0]-sum(a[1:])

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
def apply(fn,args,alist) :
    "apply a function fn to its arguments in args"
    if debug_flag :
        print("--Apply-- %s  Args=%s" % (putSexp(fn),putSexp(args)))
        printAlist(alist)

    if isSymbol(fn) :   # name of a function
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
        return eval (fn[2], pairlis(fn[1],args,alist))
    else:
        scream("Can't apply %s" % fn)

# @debug
def eval(exp, alist) :
    "evaluate an S expression using the alist"
    global Alist
    if debug_flag : print("--Eval--- %s" %  putSexp(exp)); printAlist(alist)
    if   exp == 't'     : return 't'      # true evaluates to itself
    elif exp == 'nil'   : return []       # symbol nil same as a null list
    elif exp == 'alist' : return Alist    # special command to examine alist
    elif isNumber(exp)  : return exp      # numbers eval to themselves
    elif isSymbol(exp)  : return assoc(exp,alist)  # look up variables
    else :               # check for special forms
        if exp[0] == 'quote':
            return exp[1]
        elif exp[0] == 'def' :
            # user define functions
            alist = Alist = pairlis( [exp[1]] , [exp[2]] , alist)
            return exp[1] # return function name
        elif exp[0] == 'cond':
            return evcon(exp[1:], alist)
        else:
            x = evlis(exp[1:], alist)
            return apply( exp[0], x , alist )

# @debug
def evcon (c, alist) :
    "evaluate cond. Note just the pairs passed in c"
    if   len(c) == 0           : return []
    elif eval (c[0][0], alist) : return eval (c[0][1],alist)
    else                       : return evcon(c[1:],  alist)

# @debug
def evlis(list, alist) :
    "evaluate all elements in a list, returning list of the values"
    if not list:
        return []
    else:
        return [ eval(list[0], alist) ] + evlis( list[1:], alist )

def printAlist(alist) :
    print ("Alist")
    for name,sexp in alist :
        sexp = putSexp(sexp)
        output = "(%s %s)" % (name,sexp)
        if len(output) > 50 : output = output[:50]+"..."
        print(output)

def scream(mesg) :
    print("Exiting: %s" % mesg)
    sys.exit(1)

def main() :
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
            except : scream("cant eval %s " % s)

if __name__ == "__main__" : main()