import sys

from pair import *
from scheme_utils import *
from ucb import main, trace

import scheme_forms

##############
# Eval/Apply #
##############

def scheme_eval(expr, env, _=None): # Optional third argument is ignored
    """Evaluate Scheme expression EXPR in Frame ENV.

    >>> expr = read_line('(+ 2 2)')
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> scheme_eval(expr, create_global_frame())
    4
    """
    env.stack.append(expr) # Error tracing extension
    # Evaluate atoms
    if scheme_symbolp(expr):
        result = env.lookup(expr) # Error tracing extension
        env.stack.pop()
        return result
    elif self_evaluating(expr):
        env.stack.pop() # Error tracing extension
        return expr

    # All non-atomic expressions are lists (combinations)
    if not scheme_listp(expr):
        raise SchemeError('malformed list: {0}'.format(repl_str(expr)))
    first, rest = expr.first, expr.rest
    if scheme_symbolp(first) and first in scheme_forms.SPECIAL_FORMS:
        result = scheme_forms.SPECIAL_FORMS[first](rest, env)
        env.stack.pop()
        return result
    else:
        procedure = scheme_eval(first, env)
        if isinstance(procedure, MacroProcedure):
            expr = complete_apply(procedure, rest, env)
            return scheme_eval(expr, env)
        args = rest.map(lambda operand: scheme_eval(operand, env))
        result = scheme_apply(procedure, args, env)
        env.stack.pop()
        return result

def scheme_apply(procedure, args, env):
    """Apply Scheme PROCEDURE to argument values ARGS (a Scheme list) in
    Frame ENV, the current environment."""
    validate_procedure(procedure)
    if not isinstance(env, Frame):
       assert False, "Not a Frame: {}".format(env)
    if isinstance(procedure, BuiltinProcedure):
        arguments_list = []
        while args is not nil:
            arguments_list.append(args.first)
            args = args.rest
        if procedure.need_env:
            arguments_list.append(env)
        try:
            return procedure.py_func(*arguments_list)
        except TypeError as err:
            raise SchemeError('incorrect number of arguments: {0}'.format(procedure))
    elif isinstance(procedure, LambdaProcedure):
        new_env = procedure.env.make_child_frame(procedure.formals, args)
        return eval_all(procedure.body, new_env)
    elif isinstance(procedure, MuProcedure):
        new_env = env.make_child_frame(procedure.formals, args)
        return eval_all(procedure.body, new_env)
    else:
        assert False, "Unexpected procedure: {}".format(procedure)

def eval_all(expressions, env):
    """Evaluate each expression in the Scheme list EXPRESSIONS in
    Frame ENV (the current environment) and return the value of the last.

    >>> eval_all(read_line("(1)"), create_global_frame())
    1
    >>> eval_all(read_line("(1 2)"), create_global_frame())
    2
    >>> x = eval_all(read_line("((print 1) 2)"), create_global_frame())
    1
    >>> x
    2
    >>> eval_all(read_line("((define x 2) x)"), create_global_frame())
    2
    """
    value = None
    while expressions is not nil:
        tail = expressions.rest is nil
        value = scheme_eval(expressions.first, env, tail)
        expressions = expressions.rest
    return value


##################
# Tail Recursion #
##################

class Unevaluated:
    """An expression and an environment in which it is to be evaluated."""

    def __init__(self, expr, env):
        """Expression EXPR to be evaluated in Frame ENV."""
        self.expr = expr
        self.env = env

def complete_apply(procedure, args, env):
    """Apply procedure to args in env; ensure the result is not an Unevaluated."""
    validate_procedure(procedure)
    val = scheme_apply(procedure, args, env)
    if isinstance(val, Unevaluated):
        return scheme_eval(val.expr, val.env)
    else:
        return val

def optimize_tail_calls(unoptimized_scheme_eval):
    """Return a properly tail recursive version of an eval function."""
    def optimized_eval(expr, env, tail=False):
        """Evaluate Scheme expression EXPR in Frame ENV. If TAIL,
        return an Unevaluated containing an expression for further evaluation.
        """
        if tail and not scheme_symbolp(expr) and not self_evaluating(expr):
            return Unevaluated(expr, env)

        result = Unevaluated(expr, env)
        while isinstance(result, Unevaluated):
            result = unoptimized_scheme_eval(result.expr, result.env)
        return result
    return optimized_eval

if 'doctest' not in sys.argv[0]:
    scheme_eval = optimize_tail_calls(scheme_eval)

