"""Abstract tensor product."""

from sympy import Expr, Add, Mul, Matrix, Pow, sympify
from sympy.printing.pretty.stringpict import prettyForm

from sympy.physics.quantum.qexpr import QuantumError
from sympy.physics.quantum.dagger import Dagger
from sympy.physics.quantum.commutator import Commutator
from sympy.physics.quantum.anticommutator import AntiCommutator
from sympy.physics.quantum.matrixutils import (
    numpy_ndarray,
    scipy_sparse_matrix,
    matrix_tensor_product
)

__all__ = [
    'TensorProduct',
    'tensor_product_simp'
]

#-----------------------------------------------------------------------------
# Tensor product
#-----------------------------------------------------------------------------


class TensorProduct(Expr):
    """The tensor product of two or more arguments.

    For matrices, this uses ``matrix_tensor_product`` to compute the Kronecker
    or tensor product matrix. For other objects a symbolic ``TensorProduct``
    instance is returned. The tensor product is a non-commutative
    multiplication that is used primarily with operators and states in quantum
    mechanics.

    Currently, the tensor product distinguishes between commutative and non-
    commutative arguments.  Commutative arguments are assumed to be scalars and
    are pulled out in front of the ``TensorProduct``. Non-commutative arguments
    remain in the resulting ``TensorProduct``.

    Parameters
    ==========

    args : tuple
        A sequence of the objects to take the tensor product of.

    Examples
    ========

    Start with a simple tensor product of sympy matrices::

        >>> from sympy import I, Matrix, symbols
        >>> from sympy.physics.quantum import TensorProduct

        >>> m1 = Matrix([[1,2],[3,4]])
        >>> m2 = Matrix([[1,0],[0,1]])
        >>> TensorProduct(m1, m2)
        [1, 0, 2, 0]
        [0, 1, 0, 2]
        [3, 0, 4, 0]
        [0, 3, 0, 4]
        >>> TensorProduct(m2, m1)
        [1, 2, 0, 0]
        [3, 4, 0, 0]
        [0, 0, 1, 2]
        [0, 0, 3, 4]

    We can also construct tensor products of non-commutative symbols:

        >>> from sympy import Symbol
        >>> A = Symbol('A',commutative=False)
        >>> B = Symbol('B',commutative=False)
        >>> tp = TensorProduct(A, B)
        >>> tp
        AxB

    We can take the dagger of a tensor product (note the order does NOT reverse
    like the dagger of a normal product):

        >>> from sympy.physics.quantum import Dagger
        >>> Dagger(tp)
        Dagger(A)xDagger(B)

    Expand can be used to distribute a tensor product across addition:

        >>> C = Symbol('C',commutative=False)
        >>> tp = TensorProduct(A+B,C)
        >>> tp
        (A + B)xC
        >>> tp.expand(tensorproduct=True)
        AxC + BxC
    """

    is_commutative = False

    def __new__(cls, *args, **assumptions):
        if isinstance(args[0], (Matrix, numpy_ndarray, scipy_sparse_matrix)):
            return matrix_tensor_product(*args)
        c_part, new_args = cls.flatten(sympify(args))
        c_part = Mul(*c_part)
        if len(new_args) == 0:
            return c_part
        elif len(new_args) == 1:
            return c_part*new_args[0]
        else:
            tp = Expr.__new__(cls, *new_args, **assumptions)
            return c_part*tp

    @classmethod
    def flatten(cls, args):
        # TODO: disallow nested TensorProducts.
        c_part = []
        nc_parts = []
        for arg in args:
            cp, ncp = arg.args_cnc()
            c_part.extend(list(cp))
            nc_parts.append(Mul._from_args(ncp))
        return c_part, nc_parts

    def _eval_adjoint(self):
        return TensorProduct(*[Dagger(i) for i in self.args])

    def _eval_rewrite(self, pattern, rule, **hints):
        sargs = self.args
        terms = [ t._eval_rewrite(pattern, rule, **hints) for t in sargs]
        return TensorProduct(*terms).expand(tensorproduct=True)

    def _sympystr(self, printer, *args):
        from sympy.printing.str import sstr
        length = len(self.args)
        s = ''
        for i in range(length):
            if isinstance(self.args[i], (Add, Pow, Mul)):
                s = s + '('
            s = s + sstr(self.args[i])
            if isinstance(self.args[i], (Add, Pow, Mul)):
                s = s + ')'
            if i != length-1:
                s = s + 'x'
        return s

    def _pretty(self, printer, *args):
        length = len(self.args)
        pform = printer._print('', *args)
        for i in range(length):
            next_pform = printer._print(self.args[i], *args)
            if isinstance(self.args[i], (Add, Mul)):
                next_pform = prettyForm(
                    *next_pform.parens(left='(', right=')')
                )
            pform = prettyForm(*pform.right(next_pform))
            if i != length-1:
                pform = prettyForm(*pform.right(u'\u2a02' + u' '))
        return pform

    def _latex(self, printer, *args):
        length = len(self.args)
        s = ''
        for i in range(length):
            if isinstance(self.args[i], (Add, Mul)):
                s = s + '\\left('
            # The extra {} brackets are needed to get matplotlib's latex
            # rendered to render this properly.
            s = s + '{' + printer._print(self.args[i], *args) + '}'
            if isinstance(self.args[i], (Add, Mul)):
                s = s + '\\right)'
            if i != length-1:
                s = s + '\\otimes '
        return s

    def doit(self, **hints):
        return TensorProduct(*[item.doit(**hints) for item in self.args])

    def _eval_expand_tensorproduct(self, **hints):
        """Distribute TensorProducts across addition."""
        args = self.args
        add_args = []
        stop = False
        for i in range(len(args)):
            if isinstance(args[i], Add):
                for aa in args[i].args:
                    add_args.append(
                        TensorProduct(
                            *args[:i]+(aa,)+args[i+1:]
                        ).expand(**hints)
                    )
                stop = True
            if stop: break
        if add_args:
            return Add(*add_args).expand(**hints)
        else:
            return self

    def expand(self, **hints):
        tp = TensorProduct(*[sympify(item).expand(**hints) for item in self.args])
        return Expr.expand(tp, **hints)


def tensor_product_simp_Mul(e):
    """Simplify a Mul with TensorProducts.

    Current the main use of this is to simplify a ``Mul`` of ``TensorProduct``s
    to a ``TensorProduct`` of ``Muls``. It currently only works for relatively
    simple cases where the initial ``Mul`` only has scalars and raw
    ``TensorProduct``s, not ``Add``, ``Pow``, ``Commutator``s of
    ``TensorProduct``s.

    Parameters
    ==========

    e : Expr
        A ``Mul`` of ``TensorProduct``s to be simplified.

    Returns
    =======

    e : Expr
        A ``TensorProduct`` of ``Mul``s.

    Examples
    ========

    This is an example of the type of simplification that this function
    performs::

        >>> from sympy.physics.quantum.tensorproduct import tensor_product_simp_Mul, TensorProduct
        >>> from sympy import Symbol
        >>> A = Symbol('A',commutative=False)
        >>> B = Symbol('B',commutative=False)
        >>> C = Symbol('C',commutative=False)
        >>> D = Symbol('D',commutative=False)
        >>> e = TensorProduct(A,B)*TensorProduct(C,D)
        >>> e
        AxB*CxD
        >>> tensor_product_simp_Mul(e)
        (A*C)x(B*D)

    """
    # TODO: This won't work with Muls that have other composites of
    # TensorProducts, like an Add, Pow, Commutator, etc.
    # TODO: This only works for the equivalent of single Qbit gates.
    if not isinstance(e, Mul):
        return e
    c_part, nc_part = e.args_cnc()
    n_nc = len(nc_part)
    if n_nc == 0 or n_nc == 1:
        return e
    elif e.has(TensorProduct):
        current = nc_part[0]
        if not isinstance(current, TensorProduct):
            raise TypeError('TensorProduct expected, got: %r' % current)
        n_terms = len(current.args)
        new_args = list(current.args)
        for next in nc_part[1:]:
            # TODO: check the hilbert spaces of next and current here.
            if isinstance(next, TensorProduct):
                if n_terms != len(next.args):
                    raise QuantumError(
                        'TensorProducts of different lengths: %r and %r' % \
                        (current, next)
                    )
                for i in range(len(new_args)):
                    new_args[i] = new_args[i]*next.args[i]
            else:
                # this won't quite work as we don't want next in the TensorProduct
                for i in range(len(new_args)):
                    new_args[i] = new_args[i]*next
            current = next
        return Mul(*c_part)*TensorProduct(*new_args)
    else:
        return e


def tensor_product_simp(e, **hints):
    """Try to simplify and combine TensorProducts.

    In general this will try to pull expressions inside of ``TensorProducts``.
    It currently only works for relatively simple cases where the products have
    only scalars, raw ``TensorProducts``, not ``Add``, ``Pow``, ``Commutators``
    of ``TensorProducts``. It is best to see what it does by showing examples.

    Examples
    ========

    >>> from sympy.physics.quantum import tensor_product_simp
    >>> from sympy.physics.quantum import TensorProduct
    >>> from sympy import Symbol
    >>> A = Symbol('A',commutative=False)
    >>> B = Symbol('B',commutative=False)
    >>> C = Symbol('C',commutative=False)
    >>> D = Symbol('D',commutative=False)

    First see what happens to products of tensor products:

    >>> e = TensorProduct(A,B)*TensorProduct(C,D)
    >>> e
    AxB*CxD
    >>> tensor_product_simp(e)
    (A*C)x(B*D)

    This is the core logic of this function, and it works inside, powers, sums,
    commutators and anticommutators as well:

    >>> tensor_product_simp(e**2)
    (A*C)x(B*D)**2

    """
    if isinstance(e, Add):
        return Add(*[tensor_product_simp(arg) for arg in e.args])
    elif isinstance(e, Pow):
        return tensor_product_simp(e.base)**e.exp
    elif isinstance(e, Mul):
        return tensor_product_simp_Mul(e)
    elif isinstance(e, Commutator):
        return Commutator(*[tensor_product_simp(arg) for arg in e.args])
    elif isinstance(e, AntiCommutator):
        return AntiCommutator(*[tensor_product_simp(arg) for arg in e.args])
    else:
        return e

