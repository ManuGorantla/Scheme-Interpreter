class Pair:

    def __init__(self, first, rest):
        self.first = first
        self.rest = rest

    def __repr__(self):
        return 'Pair({0}, {1})'.format(repr(self.first), repr(self.rest))

    def __str__(self):
        s = '(' + repl_str(self.first)
        rest = self.rest
        while isinstance(rest, Pair):
            s += ' ' + repl_str(rest.first)
            rest = rest.rest
        if rest is not nil:
            s += ' . ' + repl_str(rest)
        return s + ')'

    def __len__(self):
        n, rest = 1, self.rest
        while isinstance(rest, Pair):
            n += 1
            rest = rest.rest
        if rest is not nil:
            raise TypeError('length attempted on improper list')
        return n

    def __eq__(self, p):
        if not isinstance(p, Pair):
            return False
        return self.first == p.first and self.rest == p.rest

    def map(self, fn):
        """Return a Scheme list after mapping Python function FN to SELF."""
        mapped = fn(self.first)
        if self.rest is nil or isinstance(self.rest, Pair):
            return Pair(mapped, self.rest.map(fn))
        else:
            raise TypeError('ill-formed list (cdr is a promise)')

    def flatmap(self, fn):
        """Return a Scheme list after flatmapping Python function FN to SELF."""
        from scheme_builtins import scheme_append
        mapped = fn(self.first)
        if self.rest is nil or isinstance(self.rest, Pair):
            return scheme_append(mapped, self.rest.flatmap(fn))
        else:
            raise TypeError('ill-formed list (cdr is a promise)')


class nil:

    def __repr__(self):
        return 'nil'

    def __str__(self):
        return '()'

    def __len__(self):
        return 0

    def map(self, fn):
        return self

    def flatmap(self, fn):
        return self

nil = nil() 

def repl_str(val):
    if val is True:
        return "#t"
    if val is False:
        return "#f"
    if val is None:
        return "undefined"
    if isinstance(val, str) and val and val[0] == "\"":
        return "\"" + repr(val[1:-1])[1:-1] + "\""
    return str(val)
