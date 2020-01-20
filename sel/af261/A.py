"""Quantum mechanical operators.

TODO:

* Fix early 0 in apply_operators.
* Debug and test apply_operators.
* Get cse working with classes in this file.
* Doctests and documentation of special methods for InnerProduct, Commutator,
  AntiCommutator, represent, apply_operators.
"""

from sympy import Derivative, Expr
from sympy.printing.pretty.stringpict import prettyForm
from sympy.physics.quantum.dagger import Dagger
from sympy.physics.quantum.qexpr import QExpr, dispatch_method

__all__ = [
    'Operator',
    'HermitianOperator',
    'UnitaryOperator',
    'OuterProduct',
    'DifferentialOperator'
]

#-----------------------------------------------------------------------------
# Operators and outer products
#-----------------------------------------------------------------------------

class Operator(QExpr):
    """Base class for non-commuting quantum operators.

    An operator maps between quantum states [1]_. In quantum mechanics,
    observables (including, but not limited to, measured physical values) are
    represented as Hermitian operators [2]_.

    Parameters
    ==========

    args : tuple
        The list of numbers or parameters that uniquely specify the
        operator. For time-dependent operators, this will include the time.

    Examples
    ========

    Create an operator and examine its attributes::

        >>> from sympy.physics.quantum import Operator
        >>> from sympy import symbols, I
        >>> A = Operator('A')
        >>> A
        A
        >>> A.hilbert_space
        H
        >>> A.label
        (A,)
        >>> A.is_commutative
        False

    Create another operator and do some arithmetic operations::

        >>> B = Operator('B')
        >>> C = 2*A*A + I*B
        >>> C
        2*A**2 + I*B

    Operators don't commute::

        >>> A.is_commutative
        False
        >>> B.is_commutative
        False
        >>> A*B == B*A
        False

    Polymonials of operators respect the commutation properties::

        >>> e = (A+B)**3
        >>> e.expand()
        A*B*A + A*B**2 + A**2*B + A**3 + B*A*B + B*A**2 + B**2*A + B**3

    Operator inverses are handle symbolically::

        >>> A.inv()
        A**(-1)
        >>> A*A.inv()
        1

    References
    ==========

    .. [1] http://en.wikipedia.org/wiki/Operator_(physics)
    .. [2] http://en.wikipedia.org/wiki/Observable
    """

    @classmethod
    def default_args(self):
        return ("O",)
    #-------------------------------------------------------------------------
    # Printing
    #-------------------------------------------------------------------------

    _label_separator = ','

    def _print_operator_name(self, printer, *args):
        return printer._print(self.__class__.__name__, *args)

    _print_operator_name_latex = _print_operator_name

    def _print_operator_name_pretty(self, printer, *args):
        return prettyForm(self.__class__.__name__)

    def _print_contents(self, printer, *args):
        if len(self.label) == 1:
            return self._print_label(printer, *args)
        else:
            return '%s(%s)' % (
                self._print_operator_name(printer, *args),
                self._print_label(printer, *args)
            )

    def _print_contents_pretty(self, printer, *args):
        if len(self.label) == 1:
            return self._print_label_pretty(printer, *args)
        else:
            pform = self._print_operator_name_pretty(printer, *args)
            label_pform = self._print_label_pretty(printer, *args)
            label_pform = prettyForm(
                *label_pform.parens(left='(', right=')')
            )
            pform = prettyForm(*pform.right((label_pform)))
            return pform

    def _print_contents_latex(self, printer, *args):
        if len(self.label) == 1:
            return self._print_label_latex(printer, *args)
        else:
            return '%s(%s)' % (
                self._print_operator_name_latex(printer, *args),
                self._print_label_latex(printer, *args)
            )

    #-------------------------------------------------------------------------
    # _eval_* methods
    #-------------------------------------------------------------------------

    def _eval_commutator(self, other, **options):
        """Evaluate [self, other] if known, return None if not known."""
        return dispatch_method(self, '_eval_commutator', other, **options)

    def _eval_anticommutator(self, other, **options):
        """Evaluate [self, other] if known."""
        return dispatch_method(self, '_eval_anticommutator', other, **options)

    #-------------------------------------------------------------------------
    # Operator application
    #-------------------------------------------------------------------------

    def _apply_operator(self, ket, **options):
        return dispatch_method(self, '_apply_operator', ket, **options)

    def matrix_element(self, *args):
        raise NotImplementedError('matrix_elements is not defined')

    #-------------------------------------------------------------------------
    # Printing
    #-------------------------------------------------------------------------

    def inverse(self):
        return self._eval_inverse()

    inv = inverse

    def _eval_inverse(self):
        # TODO: make non-commutative Exprs print powers using A**-1, not 1/A.
        return self**(-1)


class HermitianOperator(Operator):
    """A Hermitian operator that satisfies H == Dagger(H).

    Parameters
    ==========

    args : tuple
        The list of numbers or parameters that uniquely specify the
        operator. For time-dependent operators, this will include the time.

    Examples
    ========

    >>> from sympy.physics.quantum import Dagger, HermitianOperator
    >>> H = HermitianOperator('H')
    >>> Dagger(H)
    H
    """

    is_hermitian = True

    def _eval_inverse(self):
        if isinstance(self, UnitaryOperator):
            return self
        else:
            return Operator._eval_inverse(self)

    def _eval_power(self, exp):
        if isinstance(self, UnitaryOperator):
            if exp == -1:
                return Operator._eval_power(self, exp)
            elif abs(exp) % 2 == 0:
                return self*(Operator._eval_inverse(self))
            else:
                return self
        else:
            return Operator._eval_power(self, exp)

class UnitaryOperator(Operator):
    """A unitary operator that satisfies U*Dagger(U) == 1.

    Parameters
    ==========

    args : tuple
        The list of numbers or parameters that uniquely specify the
        operator. For time-dependent operators, this will include the time.

    Examples
    ========

    >>> from sympy.physics.quantum import Dagger, UnitaryOperator
    >>> U = UnitaryOperator('U')
    >>> U*Dagger(U)
    1
    """

    def _eval_adjoint(self):
        return self._eval_inverse()


class OuterProduct(Operator):
    """An unevaluated outer product between a ket and bra.

    This constructs an outer product between any subclass of ``KetBase`` and
    ``BraBase`` as ``|a><b|``. An ``OuterProduct`` inherits from Operator as they act as
    operators in quantum expressions.  For reference see [1]_.

    Parameters
    ==========

    ket : KetBase
        The ket on the left side of the outer product.
    bar : BraBase
        The bra on the right side of the outer product.

    Examples
    ========

    Create a simple outer product by hand and take its dagger::

        >>> from sympy.physics.quantum import Ket, Bra, OuterProduct, Dagger
        >>> from sympy.physics.quantum import Operator

        >>> k = Ket('k')
        >>> b = Bra('b')
        >>> op = OuterProduct(k, b)
        >>> op
        |k><b|
        >>> op.hilbert_space
        H
        >>> op.ket
        |k>
        >>> op.bra
        <b|
        >>> Dagger(op)
        |b><k|

    In simple products of kets and bras outer products will be automatically
    identified and created::

        >>> k*b
        |k><b|

    But in more complex expressions, outer products are not automatically
    created::

        >>> A = Operator('A')
        >>> A*k*b
        A*|k>*<b|

    A user can force the creation of an outer product in a complex expression
    by using parentheses to group the ket and bra::

        >>> A*(k*b)
        A*|k><b|

    References
    ==========

    .. [1] http://en.wikipedia.org/wiki/Outer_product
    """

    is_commutative = False

    def __new__(cls, *args, **old_assumptions):
        from sympy.physics.quantum.state import KetBase, BraBase
        ket = args[0]
        bra = args[1]
        if not isinstance(ket, KetBase):
            raise TypeError('KetBase subclass expected, got: %r' % ket)
        if not isinstance(bra, BraBase):
            raise TypeError('BraBase subclass expected, got: %r' % ket)
        if not ket.dual_class() == bra.__class__:
            raise TypeError(
                'ket and bra are not dual classes: %r, %r' % \
                (ket.__class__, bra.__class__)
            )
        # TODO: make sure the hilbert spaces of the bra and ket are compatible
        obj = Expr.__new__(cls, *args, **old_assumptions)
        obj.hilbert_space = ket.hilbert_space
        return obj

    @property
    def ket(self):
        """Return the ket on the left side of the outer product."""
        return self.args[0]

    @property
    def bra(self):
        """Return the bra on the right side of the outer product."""
        return self.args[1]

    def _eval_adjoint(self):
        return OuterProduct(Dagger(self.bra), Dagger(self.ket))

    def _sympystr(self, printer, *args):
        return str(self.ket)+str(self.bra)

    def _sympyrepr(self, printer, *args):
        return '%s(%s,%s)' % (self.__class__.__name__,
            printer._print(self.ket, *args), printer._print(self.bra, *args))

    def _pretty(self, printer, *args):
        pform = self.ket._pretty(printer, *args)
        return prettyForm(*pform.right(self.bra._pretty(printer, *args)))

    def _latex(self, printer, *args):
        k = printer._print(self.ket, *args)
        b = printer._print(self.bra, *args)
        return k+b

    def _represent(self, **options):
        k = self.ket._represent(**options)
        b = self.bra._represent(**options)
        return k*b

class DifferentialOperator(Operator):
    """An operator for representing the differential operator, i.e. d/dx

    It is initialized by passing two arguments. The first is an arbitrary
    expression that involves a function, such as ``Derivative(f(x), x)``. The
    second is the function (e.g. ``f(x)``) which we are to replace with the
    ``Wavefunction`` that this ``DifferentialOperator`` is applied to.

    Parameters
    ==========

    expr : Expr
           The arbitrary expression which the appropriate Wavefunction is to be
           substituted into

    func : Expr
           A function (e.g. f(x)) which is to be replaced with the appropriate
           Wavefunction when this DifferentialOperator is applied

    Examples
    ========

    You can define a completely arbitrary expression and specify where the
    Wavefunction is to be substituted

    >>> from sympy import Derivative, Function, Symbol
    >>> from sympy.physics.quantum.operator import DifferentialOperator
    >>> from sympy.physics.quantum.state import Wavefunction
    >>> from sympy.physics.quantum.qapply import qapply
    >>> f = Function('f')
    >>> x = Symbol('x')
    >>> d = DifferentialOperator(1/x*Derivative(f(x), x), f(x))
    >>> w = Wavefunction(x**2, x)
    >>> d.function
    f(x)
    >>> d.variables
    (x,)
    >>> qapply(d*w)
    Wavefunction(2, x)

    """

    @property
    def variables(self):
        """
        Returns the variables with which the function in the specified
        arbitrary expression is evaluated

        Examples
        ========

        >>> from sympy.physics.quantum.operator import DifferentialOperator
        >>> from sympy import Symbol, Function, Derivative
        >>> x = Symbol('x')
        >>> f = Function('f')
        >>> d = DifferentialOperator(1/x*Derivative(f(x), x), f(x))
        >>> d.variables
        (x,)
        >>> y = Symbol('y')
        >>> d = DifferentialOperator(Derivative(f(x, y), x) +
        ...                          Derivative(f(x, y), y), f(x, y))
        >>> d.variables
        (x, y)
        """

        return self.args[-1].args

    @property
    def function(self):
        """
        Returns the function which is to be replaced with the Wavefunction

        Examples
        ========

        >>> from sympy.physics.quantum.operator import DifferentialOperator
        >>> from sympy import Function, Symbol, Derivative
        >>> x = Symbol('x')
        >>> f = Function('f')
        >>> d = DifferentialOperator(Derivative(f(x), x), f(x))
        >>> d.function
        f(x)
        >>> y = Symbol('y')
        >>> d = DifferentialOperator(Derivative(f(x, y), x) +
        ...                          Derivative(f(x, y), y), f(x, y))
        >>> d.function
        f(x, y)
        """

        return self.args[-1]

    @property
    def expr(self):
        """
        Returns the arbitary expression which is to have the Wavefunction
        substituted into it

        Examples
        ========

        >>> from sympy.physics.quantum.operator import DifferentialOperator
        >>> from sympy import Function, Symbol, Derivative
        >>> x = Symbol('x')
        >>> f = Function('f')
        >>> d = DifferentialOperator(Derivative(f(x), x), f(x))
        >>> d.expr
        Derivative(f(x), x)
        >>> y = Symbol('y')
        >>> d = DifferentialOperator(Derivative(f(x, y), x) +
        ...                          Derivative(f(x, y), y), f(x, y))
        >>> d.expr
        Derivative(f(x, y), x) + Derivative(f(x, y), y)
        """

        return self.args[0]

    @property
    def free_symbols(self):
        """
        Return the free symbols of the expression.
        """

        return self.expr.free_symbols

    def _apply_operator_Wavefunction(self, func):
        from sympy.physics.quantum.state import Wavefunction
        var = self.variables
        wf_vars = func.args[1:]

        f = self.function
        new_expr = self.expr.subs(f, func(*var))
        new_expr = new_expr.doit()

        return Wavefunction(new_expr, *wf_vars)

    def _eval_derivative(self, symbol):
        new_expr = Derivative(self.expr, symbol)
        return DifferentialOperator(new_expr, self.args[-1])

    #-------------------------------------------------------------------------
    # Printing
    #-------------------------------------------------------------------------

    def _print_contents(self, printer, *args):
        return '%s(%s)' % (
            self._print_operator_name(printer, *args),
            self._print_label(printer, *args)
          )

    def _print_contents_pretty(self, printer, *args):
        pform = self._print_operator_name_pretty(printer, *args)
        label_pform = self._print_label_pretty(printer, *args)
        label_pform = prettyForm(
            *label_pform.parens(left='(', right=')')
        )
        pform = prettyForm(*pform.right((label_pform)))
        return pform
