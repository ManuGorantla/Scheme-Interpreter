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

        env.define(signature, scheme_eval(expressions.rest.first, env))

        return signature
    elif isinstance(signature, Pair) and scheme_symbolp(signature.first):
        # defining a named procedure 
        "*** YOUR CODE HERE ***"
        validate_formals (signature. rest)
        result = signature.first
        lambda_procedure = LambdaProcedure(signature.rest, expressions. rest, env)
        env. define(result, lambda_procedure)
        return result
    else:
        bad_signature = signature.first if isinstance(signature, Pair) else signature
        raise SchemeError('non-symbol: {0}'.format(bad_signature))

def do_quote_form(expressions, env):
    """Evaluate a quote form.
    """
    validate_form(expressions, 1, 1)
    if expressions.rest == nil:
        return expressions.first
    
    return expressions

def do_begin_form(expressions, env):
    """Evaluate a begin form.
    """
    validate_form(expressions, 1)
    return eval_all(expressions, env)

def do_lambda_form(expressions, env):
    """Evaluate a lambda form.

    
    """
    validate_form(expressions, 2)
    formals = expressions.first
    validate_formals(formals)
    return LambdaProcedure(formals, expressions.rest, env)

def do_if_form(expressions, env):
    """Evaluate an if form. """
    validate_form(expressions, 2, 3)
    if is_scheme_true(scheme_eval(expressions.first, env)):
        return scheme_eval(expressions.rest.first, env)
    elif len(expressions) == 3:
        return scheme_eval(expressions.rest.rest.first, env)

def do_and_form(expressions, env):
    """Evaluate a (short-circuited) and form.
    """
    if len(expressions) == 0:
        return True
    elif len(expressions) == 1:
        return scheme_eval(expressions.first, env)
    elif is_scheme_true(scheme_eval(expressions.first, env)):
        return do_and_form(expressions.rest, env)
    else:
        return scheme_eval(expressions.first, env)


def do_or_form(expressions, env):
    """Evaluate a (short-circuited) or form.

    """
  
    if len(expressions) == 0:
        return False
    elif len(expressions) == 1:
        return scheme_eval(expressions.first, env)
    elif is_scheme_true(scheme_eval(expressions.first, env)):
        return scheme_eval(expressions.first, env)
    else:
        return do_or_form(expressions.rest, env)

def do_cond_form(expressions, env):
    """Evaluate a cond form.
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
            "*** YOUR CODE HERE ***"
            if clause.rest == nil:
                return test
            else:
                return eval_all(clause.rest, env)
        expressions = expressions.rest

def do_let_form(expressions, env):
    """Evaluate a let form.
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
    x = bindings

    while x != nil:
        validate_form(x.first, 2, 2)
        names = Pair(x.first.first, names)
        vals = Pair(eval_all(x.first.rest, env), vals)
        x = x.rest
    
    validate_formals(names)
    return env.make_child_frame(names, vals)



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
    return MuProcedure (formals, expressions. rest)



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
    'quasiquote': do_quasiquote_form,
    'unquote': do_unquote,
    'mu': do_mu_form,
}
