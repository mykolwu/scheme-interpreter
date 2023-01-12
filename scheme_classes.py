import builtins

from pair import *

class SchemeError(Exception):
    """Exception indicating an error in a Scheme program."""

################
# Environments #
################

class Frame:
    """An environment frame binds Scheme symbols to Scheme values."""

    def __init__(self, parent):
        """An empty frame with parent frame PARENT (which may be None)."""
        self.bindings = {}
        self.parent = parent
        if self.parent: # Error tracing extension
            self.stack = self.parent.stack
        else:
            self.stack = []

    def __repr__(self):
        if self.parent is None:
            return '<Global Frame>'
        s = sorted(['{0}: {1}'.format(k, v) for k, v in self.bindings.items()])
        return '<{{{0}}} -> {1}>'.format(', '.join(s), repr(self.parent))

    def define(self, symbol, value):
        """Define Scheme SYMBOL to have VALUE."""
        self.bindings[symbol] = value

    def lookup(self, symbol):
        """Return the value bound to SYMBOL. Errors if SYMBOL is not found."""
        e = self
        while e is not None:
            if symbol in e.bindings:
                return e.bindings[symbol]
            e = e.parent
        raise SchemeError('unknown identifier: {0}'.format(symbol))


    def rebind(self, symbol, value):
        """Rebind SYMBOL to VALUE in the first frame in which SYMBOL is bound.
        Errors if SYMBOL is not found."""
        e = self
        while e is not None:
            if symbol in e.bindings:
                e.define(symbol, value)
                return
            e = e.parent
        raise SchemeError('unknown identifier: {0}'.format(symbol))

    def make_child_frame(self, formals, vals):
        """Return a new local frame whose parent is SELF, in which the symbols
        in a Scheme list of formal parameters FORMALS are bound to the Scheme
        values in the Scheme list VALS. Both FORMALS and VALS are represented
        as Pairs. Raise an error if too many or too few vals are given.

        >>> env = create_global_frame()
        >>> formals, expressions = read_line('(a b c)'), read_line('(1 2 3)')
        >>> env.make_child_frame(formals, expressions)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>
        """
        if len(formals) != len(vals):
            raise SchemeError('Incorrect number of arguments to function call')
        from scheme_builtins import scheme_variadic_symbolp, scheme_variadic_symbol
        child = Frame(self) # Create a new child with self as the parent
        while formals != nil and vals != nil:
            # handle variadic functions (not required)
            if scheme_variadic_symbolp(formals.first):
                assert formals.rest is nil, "should have been caught earlier"
                child.define(scheme_variadic_symbol(formals.first), vals)
                return child
            if vals is nil:
                raise SchemeError('too few arguments to function call')

            # bind formal parameters to their values (required)
            child.define(formals.first, vals.first)
            formals, vals = formals.rest, vals.rest
        if formals != nil and scheme_variadic_symbolp(formals.first):
            assert formals.rest is nil, "should have been caught earlier"
            child.define(scheme_variadic_symbol(formals.first), vals)
            return child
        if formals != nil or vals != nil:
                raise SchemeError('Incorrect number of arguments to function call')
        # Handle dotted parameters list (only for backwards compatibility with DOTS_ARE_CONS)
        if formals != nil:
            child.define(formals, vals)
        elif vals != nil:
            raise SchemeError('too many arguments to function call')
        return child

##############
# Procedures #
##############

class Procedure:
    """The the base class for all Procedure classes."""

class BuiltinProcedure(Procedure):
    """A Scheme procedure defined as a Python function."""

    def __init__(self, py_func, need_env=False, name='builtin'):
        self.name = name
        self.py_func = py_func
        self.need_env = need_env

    def __str__(self):
        return '#[{0}]'.format(self.name)

class LambdaProcedure(Procedure):
    """A procedure defined by a lambda expression or a define form."""
    name = '[lambda]' # Error tracing extension

    def __init__(self, formals, body, env):
        """A procedure with formal parameter list FORMALS (a Scheme list),
        whose body is the Scheme list BODY, and whose parent environment
        starts with Frame ENV."""
        assert isinstance(env, Frame), "env must be of type Frame"

        from scheme_utils import validate_type, scheme_listp
        validate_type(formals, scheme_listp, 0, 'LambdaProcedure')
        validate_type(body, scheme_listp, 1, 'LambdaProcedure')
        self.formals = formals
        self.body = body
        self.env = env

    def __str__(self):
        return str(Pair('lambda', Pair(self.formals, self.body)))

    def __repr__(self):
        return 'LambdaProcedure({0}, {1}, {2})'.format(
            repr(self.formals), repr(self.body), repr(self.env))

class MuProcedure(Procedure):
    """A procedure defined by a mu expression, which has dynamic scope.
     _________________
    < Scheme is cool! >
     -----------------
            \   ^__^
             \  (oo)\_______
                (__)\       )\/\
                    ||----w |
                    ||     ||
    """
    name = '[mu]' # Error tracing extension

    def __init__(self, formals, body):
        """A procedure with formal parameter list FORMALS (a Scheme list) and
        Scheme list BODY as its definition."""
        self.formals = formals
        self.body = body

    def __str__(self):
        return str(Pair('mu', Pair(self.formals, self.body)))

    def __repr__(self):
        return 'MuProcedure({0}, {1})'.format(
            repr(self.formals), repr(self.body))

class MacroProcedure(LambdaProcedure):
    """A macro: a special form that operates on its unevaluated operands to
    create an expression that is evaluated in place of a call."""


###########
# Streams #
###########

class Promise:
    """A promise."""
    def __init__(self, expression, env):
        self.expression = expression
        self.env = env

    def evaluate(self):
        from scheme_eval_apply import scheme_eval # FIXME
        if self.expression is not None:
            value = scheme_eval(self.expression, self.env)
            if not builtins.DOTS_ARE_CONS and not (value is nil or isinstance(value, Pair)):
                raise SchemeError("result of forcing a promise should be a pair or nil, but was %s" % value)
            self.value = value
            self.expression = None
        return self.value

    def __str__(self):
        return '#[promise ({0}forced)]'.format(
                'not ' if self.expression is not None else '')

