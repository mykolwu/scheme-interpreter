from scheme_eval_apply import *
from scheme_utils import *
from scheme_classes import *
from scheme_builtins import *

#################
# Special Forms #
#################

# Each of the following do_xxx_form functions takes the cdr of a special form as
# its first argument---a Scheme list representing a special form without the
# initial identifying symbol (if, lambda, quote, ...). Its second argument is
# the environment in which the form is to be evaluated.

def do_define_form(expressions, env):
    """Evaluate a define form.
    >>> env = create_global_frame()
    >>> do_define_form(read_line("(x 2)"), env) # evaluating (define x 2)
    'x'
    >>> scheme_eval("x", env)
    2
    >>> do_define_form(read_line("(x (+ 2 8))"), env) # evaluating (define x (+ 2 8))
    'x'
    >>> scheme_eval("x", env)
    10
    >>> # problem 10
    >>> env = create_global_frame()
    >>> do_define_form(read_line("((f x) (+ x 2))"), env) # evaluating (define (f x) (+ x 8))
    'f'
    >>> scheme_eval(read_line("(f 3)"), env)
    5
    """
    validate_form(expressions, 2) # Checks that expressions is a list of length at least 2
    signature = expressions.first
    if scheme_symbolp(signature):
        # assigning a name to a value e.g. (define x (+ 1 2))
        validate_form(expressions, 2, 2) # Checks that expressions is a list of length exactly 2
        value = scheme_eval(expressions.rest.first, env)
        env.define(signature, value)
        return signature
    elif isinstance(signature, Pair) and scheme_symbolp(signature.first):
        # defining a named procedure e.g. (define (f x y) (+ x y))
        name = signature.first
        formals = signature.rest
        body = expressions.rest
        value = do_lambda_form(Pair(formals, body), env)
        value.name = name # Error tracing extension
        env.define(name, value)
        return name
    else:
        bad_signature = signature.first if isinstance(signature, Pair) else signature
        raise SchemeError('non-symbol: {0}'.format(bad_signature))

def do_quote_form(expressions, env):
    """Evaluate a quote form.

    >>> env = create_global_frame()
    >>> do_quote_form(read_line("((+ x 2))"), env) # evaluating (quote (+ x 2))
    Pair('+', Pair('x', Pair(2, nil)))
    """
    validate_form(expressions, 1, 1)
    return expressions.first

def do_begin_form(expressions, env):
    """Evaluate a begin form.

    >>> env = create_global_frame()
    >>> x = do_begin_form(read_line("((print 2) 3)"), env) # evaluating (begin (print 2) 3)
    2
    >>> x
    3
    """
    validate_form(expressions, 1)
    return eval_all(expressions, env)

def do_lambda_form(expressions, env):
    """Evaluate a lambda form.

    >>> env = create_global_frame()
    >>> do_lambda_form(read_line("((x) (+ x 2))"), env) # evaluating (lambda (x) (+ x 2))
    LambdaProcedure(Pair('x', nil), Pair(Pair('+', Pair('x', Pair(2, nil))), nil), <Global Frame>)
    """
    validate_form(expressions, 2)
    formals = expressions.first
    validate_formals(formals)
    return LambdaProcedure(formals, expressions.rest, env)

def do_if_form(expressions, env):
    """Evaluate an if form.

    >>> env = create_global_frame()
    >>> do_if_form(read_line("(#t (print 2) (print 3))"), env) # evaluating (if #t (print 2) (print 3))
    2
    >>> do_if_form(read_line("(#f (print 2) (print 3))"), env) # evaluating (if #f (print 2) (print 3))
    3
    """
    validate_form(expressions, 2, 3)
    if is_scheme_true(scheme_eval(expressions.first, env)):
        return scheme_eval(expressions.rest.first, env, True)
    elif len(expressions) == 3:
        return scheme_eval(expressions.rest.rest.first, env, True)

def do_and_form(expressions, env):
    """Evaluate a (short-circuited) and form.

    >>> env = create_global_frame()
    >>> do_and_form(read_line("(#f (print 1))"), env) # evaluating (and #f (print 1))
    False
    >>> # evaluating (and (print 1) (print 2) (print 4) 3 #f)
    >>> do_and_form(read_line("((print 1) (print 2) (print 3) (print 4) 3 #f)"), env)
    1
    2
    3
    4
    False
    """
    value = True
    while expressions is not nil:
        tail = expressions.rest is nil
        value = scheme_eval(expressions.first, env, tail)
        if is_scheme_false(value):
            return value
        expressions = expressions.rest
    return value

def do_or_form(expressions, env):
    """Evaluate a (short-circuited) or form.

    >>> env = create_global_frame()
    >>> do_or_form(read_line("(10 (print 1))"), env) # evaluating (or 10 (print 1))
    10
    >>> do_or_form(read_line("(#f 2 3 #t #f)"), env) # evaluating (or #f 2 3 #t #f)
    2
    >>> # evaluating (or (begin (print 1) #f) (begin (print 2) #f) 6 (begin (print 3) 7))
    >>> do_or_form(read_line("((begin (print 1) #f) (begin (print 2) #f) 6 (begin (print 3) 7))"), env)
    1
    2
    6
    """
    value = False
    while expressions is not nil:
        tail = expressions.rest is nil
        value = scheme_eval(expressions.first, env, tail)
        if is_scheme_true(value):
            return value
        expressions = expressions.rest
    return value

def do_cond_form(expressions, env):
    """Evaluate a cond form.

    >>> do_cond_form(read_line("((#f (print 2)) (#t 3))"), create_global_frame())
    3
    """
    while expressions is not nil:
        clause = expressions.first
        validate_form(clause, 1)
        if clause.first == 'else':
            test = True
            if expressions.rest != nil:
                raise SchemeError('else must be last')
        else:
            test = scheme_eval(clause.first, env)
        if is_scheme_true(test):
            if len(clause) == 1:
                return test
            else:
                return eval_all(clause.rest, env)
        expressions = expressions.rest

def do_let_form(expressions, env):
    """Evaluate a let form.

    >>> env = create_global_frame()
    >>> do_let_form(read_line("(((x 2) (y 3)) (+ x y))"), env)
    5
    """
    validate_form(expressions, 2)
    let_env = make_let_frame(expressions.first, env)
    return eval_all(expressions.rest, let_env)

def make_let_frame(bindings, env):
    """Create a child frame of Frame ENV that contains the definitions given in
    BINDINGS. The Scheme list BINDINGS must have the form of a proper bindings
    list in a let expression: each item must be a list containing a symbol
    and a Scheme expression."""
    if not scheme_listp(bindings):
        raise SchemeError('bad bindings list in let form')
    names = vals = nil
    while bindings is not nil:
        binding = bindings.first
        validate_form(binding, 2, 2)
        name = binding.first
        val = scheme_eval(binding.rest.first, env)
        names = Pair(name, names)
        vals = Pair(val, vals)
        bindings = bindings.rest
    validate_formals(names)
    return env.make_child_frame(names, vals)


def do_define_macro(expressions, env):
    """Evaluate a define-macro form.

    >>> env = create_global_frame()
    >>> do_define_macro(read_line("((f x) (car x))"), env)
    'f'
    >>> scheme_eval(read_line("(f (1 2))"), env)
    1
    """
    validate_form(expressions, 2)
    signature = expressions.first

    if isinstance(signature, Pair) and scheme_symbolp(signature.first):
        name = signature.first
        formals = signature.rest
        body = expressions.rest
        validate_formals(formals)
        value = MacroProcedure(formals, body, env)
        value.name = name # Error tracing extension
        env.define(name, value)
        return name
    else:
        raise SchemeError('improper form for define-macro')


def do_quasiquote_form(expressions, env):
    """Evaluate a quasiquote form with parameters EXPRESSIONS in
    Frame ENV."""
    def quasiquote_item(val, env, level):
        """Evaluate Scheme expression VAL that is nested at depth LEVEL in
        a quasiquote form in Frame ENV."""
        if not scheme_pairp(val):
            return val
        if val.first == 'unquote':
            level -= 1
            if level == 0:
                expressions = val.rest
                validate_form(expressions, 1, 1)
                return scheme_eval(expressions.first, env)
        elif val.first == 'quasiquote':
            level += 1

        return val.map(lambda elem: quasiquote_item(elem, env, level))

    validate_form(expressions, 1, 1)
    return quasiquote_item(expressions.first, env, 1)

def do_unquote(expressions, env):
    raise SchemeError('unquote outside of quasiquote')


#################
# Dynamic Scope #
#################

def do_mu_form(expressions, env):
    """Evaluate a mu form."""
    validate_form(expressions, 2)
    formals = expressions.first
    validate_formals(formals)
    return MuProcedure(formals, expressions.rest)

def do_delay_form(expressions, env):
    """Evaluates a delay form."""
    validate_form(expressions, 1, 1)
    return Promise(expressions.first, env)

def do_cons_stream_form(expressions, env):
    """Evaluate a cons-stream form."""
    validate_form(expressions, 2, 2)
    return Pair(scheme_eval(expressions.first, env),
                do_delay_form(expressions.rest, env))


def indent(s, pad=4):
    return "\n".join(" " * pad + line for line in s.split("\n"))


def do_set_form(expressions, env):
    """Evaluate set! form with parameters EXPRESSIONS in Frame ENV."""
    validate_form(expressions, 2)
    name = expressions.first
    if not scheme_symbolp(name):
        raise SchemeError('bad argument: ' + repl_str(name))
    value = scheme_eval(expressions.rest.first, env)
    env.rebind(name, value)

# Alternate quasiquote form that supports unquote-splicing
def do_quasiquote_form(expressions, env):
    """Evaluate a quasiquote form with parameters EXPRESSIONS in
    Frame ENV."""
    validate_form(expressions, 1, 1)

    def quasiquote_item(val, level=1):
        """Evaluate Scheme expression VAL that is nested at depth LEVEL in
        a quasiquote form in Frame ENV.  Returns list of values that
        should be spliced into the parent list"""
        if scheme_pairp(val):
            if val.first in ('unquote', 'unquote-splicing'):
                level -= 1
                if level == 0:
                    expressions = val.rest
                    validate_form(expressions, 1, 1)
                    evaluated = scheme_eval(expressions.first, env)
                    splice = val.first == 'unquote-splicing'
                    if splice and not scheme_listp(evaluated):
                        msg = 'unquote-splicing used on non-list: {0}'
                        raise SchemeError(msg.format(evaluated))
                    return evaluated if splice else Pair(evaluated, nil)
            elif val.first == 'quasiquote':
                level += 1

            return Pair(val.flatmap(lambda elem: quasiquote_item(elem, level)), nil)
        else:
            return Pair(val, nil)

    if scheme_pairp(expressions.first) and expressions.first.first == "unquote-splicing":
        msg = 'unquote-splicing not in list template: {0}'
        raise SchemeError(msg.format(expressions.first))
    return quasiquote_item(expressions.first).first

def do_variadic(expressions, env):
    raise SchemeError('Cannot evaluate variadic symbol')

def check_json_out(env):
    try:
        env.lookup("__run_all_doctests")
        return True
    except SchemeError:
        return False


def do_expect(expressions, env):
    validate_form(expressions, 2, 2)
    json = check_json_out(env)
    raw = []
    out = raw.append
    success = False
    try:
        old_stack = env.stack[:]
        env.stack[:] = []
        ret = scheme_eval(expressions.first, env)
    except Exception as e:
        out("Test failed:")
        out(indent("scm> " + repl_str(expressions.first), pad=4))
        out("Expected:")
        out(indent(repl_str(expressions.rest.first), pad=4))
        out("Received:")
        handle_error(env, out)
        out("Error: " + str(e))
    else:
        if scheme_equalp(ret, expressions.rest.first):
            success = True
            out("scm> " + repl_str(expressions.first) + "; received " + repl_str(expressions.rest.first) + ", success")
        else:
            out("Test failed:")
            out(indent("scm> " + repl_str(expressions.first), pad=4))
            out("Expected:")
            out(indent(repl_str(expressions.rest.first), pad=4))
            out("Received:")
            out(indent(repl_str(ret)))
    finally:
        env.stack[:] = old_stack

    if json:
        print("DOCTEST: " + json_repr(dict(
            name=["Doctests", repl_str(expressions.first)],
            rawName="Doctests > " + repl_str(expressions.first),
            success=success,
            code=[repl_str(expressions.first)],
            raw="\n".join(raw)
        )), end="")
    else:
        if success:
            print("\n".join(raw))
        else:
            print("\n".join(raw), file=sys.stderr)

def do_case(expressions, env):
    validate_form(expressions, 1, 1)
    scheme_display("# ")
    scheme_displayln(scheme_eval(expressions.first, env))


SPECIAL_FORMS = {
    'and': do_and_form,
    'begin': do_begin_form,
    'cond': do_cond_form,
    'define': do_define_form,
    'if': do_if_form,
    'lambda': do_lambda_form,
    'let': do_let_form,
    'or': do_or_form,
    'quote': do_quote_form,
    'define-macro': do_define_macro,
    'quasiquote': do_quasiquote_form,
    'unquote': do_unquote,
    'mu': do_mu_form,
    'cons-stream': do_cons_stream_form,
    'delay': do_delay_form,
    'set!': do_set_form,
    'unquote-splicing': do_unquote,
    "variadic": do_variadic,
    "expect": do_expect,
    "!": do_case,
}