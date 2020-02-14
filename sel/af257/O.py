from sympy import Symbol, Rational, ln, exp, log, sqrt, E, O, pi, I, sinh, \
        sin, cosh, cos, tanh, coth, asinh, acosh, atanh, acoth, tan, Integer, \
        PoleError, floor, ceiling, raises, asin, symbols
from sympy.abc import x, y, z

def test_simple_1():
    assert x.nseries(x, 0, 5) == x
    assert y.nseries(x, 0, 5) == y
    assert (1/(x*y)).nseries(y, 0, 5) == 1/(x*y)
    assert Rational(3,4).nseries(x, 0, 5) == Rational(3,4)

def test_mul_0():
    assert (x*ln(x)).nseries(x, 0, 5) == x*ln(x)

def test_mul_1():
    assert (x*ln(2+x)).nseries(x, 0, 4) == x*log(2)+x**2/2-x**3/8+x**4/24+ \
            O(x**5)
    assert (x*ln(1+x)).nseries(x, 0, 4) == x**2- x**3/2 + x**4/3 + O(x**5)

def test_pow_0():
    assert (x**2).nseries(x, 0, 5) == x**2
    assert (1/x).nseries(x, 0, 5) == 1/x
    assert (1/x**2).nseries(x, 0, 5) == 1/x**2
    assert (x**(Rational(2,3))).nseries(x, 0, 5) == (x**(Rational(2,3)))
    assert (x**(Rational(3,2))).nseries(x, 0, 5) == (x**(Rational(3,2)))

def test_pow_1():
    assert ((1+x)**2).nseries(x, 0, 5) == 1+2*x+x**2

def test_geometric_1():
    assert (1/(1-x)).nseries(x, 0, 5) == 1+x+x**2+x**3+x**4+O(x**5)
    assert (x/(1-x)).nseries(x, 0, 5) == x+x**2+x**3+x**4+x**5+O(x**6)
    assert (x**3/(1-x)).nseries(x, 0, 5) == x**3+x**4+x**5+x**6+x**7+O(x**8)

def test_sqrt_1():
    assert sqrt(1+x).nseries(x, 0, 5) == 1+x/2-x**2/8+x**3/16-5*x**4/128+O(x**5)

def test_exp_1():
    assert exp(x).nseries(x, 0, 5) == 1+x+x**2/2+x**3/6+x**4/24 + O(x**5)
    assert exp(x).nseries(x, 0, 12) == 1+x+x**2/2+x**3/6+x**4/24+x**5/120+  \
            x**6/720+x**7/5040+x**8/40320+x**9/362880+x**10/3628800+  \
            x**11/39916800 + O(x**12)
    assert exp(1/x).nseries(x, 0, 5) == exp(1/x)
    assert exp(1/(1+x)).nseries(x, 0, 4) ==  \
            (E*(1-x-13*x**3/6+3*x**2/2)).expand() + O(x**4)
    assert exp(2+x).nseries(x, 0, 5) ==  \
            (exp(2)*(1+x+x**2/2+x**3/6+x**4/24)).expand() + O(x**5)

def test_exp_sqrt_1():
    assert exp(1+sqrt(x)).nseries(x, 0, 3) ==  \
        (exp(1)*(1+sqrt(x)+x/2+sqrt(x)*x/6)).expand() + O(sqrt(x)**3)

def test_power_x_x1():
    assert (exp(x*ln(x))).nseries(x, 0, 4) == \
            1+x*log(x)+x**2*log(x)**2/2+x**3*log(x)**3/6 + O(x**4*log(x)**4)

def test_power_x_x2():
    assert (x**x).nseries(x, 0, 4) == \
            1+x*log(x)+x**2*log(x)**2/2+x**3*log(x)**3/6 + O(x**4*log(x)**4)

def test_log_singular1():
    assert log(1+1/x).nseries(x, 0, 5) == x - log(x) - x**2/2 + x**3/3 - \
            x**4/4 + O(x**5)

def test_log_power1():
    e = 1 / (1/x + x ** (log(3)/log(2)))
    assert e.nseries(x, 0, 5) == x - x**(2 + log(3)/log(2)) + O(x**5)

def test_log_series():
    e = 1/(1-log(x))
    assert e.nseries(x, 0, 5) == -1/log(x) - log(x)**(-2) - log(x)**(-3) - \
            log(x)**(-4) + O(log(x)**(-5))

def test_log2():
    e = log(-1/x)
    assert e.nseries(x, 0, 5) == -log(x) + log(-1)

def test_log3():
    e = 1/log(-1/x)
    assert e.nseries(x, 0, 4) == -1/log(x) - pi*I*log(x)**(-2) + \
        pi**2*log(x)**(-3) + O(log(x)**(-4))

def test_series1():
    x = Symbol("x")
    e = sin(x)
    assert e.nseries(x,0,0) != 0
    assert e.nseries(x,0,0) == O(1, x)
    assert e.nseries(x,0,1) == O(x, x)
    assert e.nseries(x,0,2) == x + O(x**2, x)
    assert e.nseries(x,0,3) == x + O(x**3, x)
    assert e.nseries(x,0,4) == x-x**3/6 + O(x**4, x)

    e = (exp(x)-1)/x
    assert e.nseries(x,0,3) == 1+x/2+O(x**2, x)

    #assert x.nseries(x,0,0) == O(1, x)
    #assert x.nseries(x,0,1) == O(x, x)
    assert x.nseries(x,0,2) == x

def test_seriesbug1():
    x = Symbol("x")
    assert (1/x).nseries(x,0,3) == 1/x
    assert (x+1/x).nseries(x,0,3) == x+1/x

def test_series2x():
    x = Symbol("x")
    assert ((x+1)**(-2)).nseries(x,0,4) == 1-2*x+3*x**2-4*x**3+O(x**4, x)
    assert ((x+1)**(-1)).nseries(x,0,4) == 1-x+x**2-x**3+O(x**4, x)
    assert ((x+1)**0).nseries(x,0,3) == 1
    assert ((x+1)**1).nseries(x,0,3) == 1+x
    assert ((x+1)**2).nseries(x,0,3) == 1+2*x+x**2
    assert ((x+1)**3).nseries(x,0,3) == 1+3*x+3*x**2+x**3

    assert (1/(1+x)).nseries(x,0,4) == 1-x+x**2-x**3+O(x**4, x)
    assert (x+3/(1+2*x)).nseries(x,0,4) == 3-5*x+12*x**2-24*x**3+O(x**4, x)

    assert ((1/x+1)**3).nseries(x,0,3)== 1+x**(-3)+3*x**(-2)+3/x
    assert (1/(1+1/x)).nseries(x,0,4) == x-x**2+x**3-O(x**4, x)
    assert (1/(1+1/x**2)).nseries(x,0,6) == x**2-x**4+O(x**6, x)

def test_bug2(): ### 1/log(0) * log(0) problem
    w = Symbol("w", nonnegative=True)
    e = (w**(-1)+w**(-log(3)*log(2)**(-1)))**(-1)*(3*w**(-log(3)*log(2)**(-1))+2*w**(-1))
    e = e.expand()
    #should be 3, but is 2
    assert e.nseries(w,0,4).subs(w,0)==3

def test_exp():
    x = Symbol("x")
    e = (1+x)**(1/x)
    assert e.nseries(x, 0, 3) == exp(1) - x*exp(1)/2 + O(x**2, x)

def test_exp2():
    x = Symbol("x")
    w = Symbol("w")
    e = w**(1-log(x)/(log(2) + log(x)))
    assert e.nseries(w,0,1) == e

def test_bug3():
    x = Symbol("x")
    e = (2/x+3/x**2)/(1/x+1/x**2)
    assert e.nseries(x, 0, 3) == 3 + O(x)

def test_generalexponent():
    x = Symbol("x")
    p = 2
    e = (2/x+3/x**p)/(1/x+1/x**p)
    assert e.nseries(x,0,3) == 3 + O(x)
    p = Rational(1,2)
    e = (2/x+3/x**p)/(1/x+1/x**p)
    assert e.nseries(x,0,2) == 2 + sqrt(x) + O(x)

    e=1+x**Rational(1,2)
    assert e.nseries(x,0,4) == 1+x**Rational(1,2)

# more complicated example
def test_genexp_x():
    x = Symbol("x")
    e=1/(1+x**Rational(1,2))
    assert e.nseries(x,0,2) == \
                1+x-x**Rational(1,2)-x**Rational(3,2)+O(x**2, x)

# more complicated example
def test_genexp_x2():
    x = Symbol("x", nonnegative=True)
    p = Rational(3,2)
    e = (2/x+3/x**p)/(1/x+1/x**p)
    assert e.nseries(x,0,3) == 3 - sqrt(x) + x + O(sqrt(x)**3)

def test_seriesbug2():
    w = Symbol("w")
    #simple case (1):
    e = ((2*w)/w)**(1+w)
    assert e.nseries(w,0,1) == 2 + O(w, w)
    assert e.nseries(w,0,1).subs(w,0) == 2

def test_seriesbug2b():
    w = Symbol("w")
    #test sin
    e = sin(2*w)/w
    assert e.nseries(w,0,3) == 2 + O(w**2, w)

def test_seriesbug2d():
    w = Symbol("w", real=True)
    e = log(sin(2*w)/w)
    assert e.nseries(w, 0, 5) == log(2) - 2*w**2/3 - 4*w**4/45 + O(w**5)

def test_seriesbug2c():
    w = Symbol("w", real=True)
    #more complicated case, but sin(x)~x, so the result is the same as in (1)
    e=(sin(2*w)/w)**(1+w)
    assert e.nseries(w,0,1) == 2 + O(w)
    assert e.nseries(w,0,3) == 2-Rational(4,3)*w**2+w**2*log(2)**2+2*w*log(2)+O(w**3, w)
    assert e.nseries(w,0,2).subs(w,0) == 2

def test_expbug4():
    x = Symbol("x", real=True)
    assert (log(sin(2*x)/x)*(1+x)).nseries(x,0,2) == log(2) + x*log(2) + O(x**2, x)
    #assert exp(log(2)+O(x)).nseries(x,0,2) == 2 +O(x**2, x)
    assert exp(log(sin(2*x)/x)*(1+x)).nseries(x,0,2) == 2 + 2*x*log(2) + O(x**2)
    #assert ((2+O(x))**(1+x)).nseries(x,0,2) == 2 + O(x**2, x)

def test_logbug4():
    x = Symbol("x")
    assert log(2+O(x)).nseries(x,0,2) == log(2) + O(x, x)

def test_expbug5():
    x = Symbol("x")
    #assert exp(O(x)).nseries(x,0,2) == 1 + O(x**2, x)
    assert exp(log(1+x)/x).nseries(x, 0, 3) == exp(1) + -exp(1)*x/2 + O(x**2)

def test_sinsinbug():
    x = Symbol("x")
    assert sin(sin(x)).nseries(x,0,8) == x-x**3/3+x**5/10-8*x**7/315+O(x**8)

def test_issue159():
    x = Symbol("x")
    a=x/(exp(x)-1)
    assert a.nseries(x,0,6) == 1 - x/2 - x**4/720 + x**2/12 + O(x**5)

def test_issue105():
    x = Symbol("x", nonnegative=True)
    f = sin(x**3)**Rational(1,3)
    assert f.nseries(x,0,17) == x - x**7/18 - x**13/3240 + O(x**17)

def test_issue125():
    y = Symbol("y")
    f=(1-y**(Rational(1)/2))**(Rational(1)/2)
    assert f.nseries(y,0,2) == 1 - sqrt(y)/2-y/8-y**Rational(3,2)/16+O(y**2)

def test_issue364():
    w = Symbol("w")
    x = Symbol("x")
    e = 1/x*(-log(w**(1 + 1/log(3)*log(5))) + log(w + w**(1/log(3)*log(5))))
    e_ser = -log(5)*log(w)/(x*log(3)) + w**(log(5)/log(3) - 1)/x - \
            w**(2*log(5)/log(3) - 2)/(2*x) + O(w)
    assert e.nseries(w, 0, 1) == e_ser

def test_sin():
    x = Symbol("x")
    y = Symbol("y")
    assert sin(8*x).nseries(x, 0, 4) == 8*x - 256*x**3/3 + O(x**4)
    assert sin(x+y).nseries(x, 0, 1) == sin(y) + O(x)
    assert sin(x+y).nseries(x, 0, 2) == sin(y) + cos(y)*x + O(x**2)
    assert sin(x+y).nseries(x, 0, 5) == sin(y) + cos(y)*x - sin(y)*x**2/2 - \
        cos(y)*x**3/6 + sin(y)*x**4/24 + O(x**5)

def test_issue416():
    x = Symbol("x")
    e = sin(8*x)/x
    assert e.nseries(x, 0, 6) == 8 - 256*x**2/3 + 4096*x**4/15 + O(x**5)

def test_issue406():
    x = Symbol("x")
    e = sin(x)**(-4)*(cos(x)**Rational(1,2)*sin(x)**2 - \
            cos(x)**Rational(1,3)*sin(x)**2)
    assert e.nseries(x, 0, 8) == -Rational(1)/12 - 7*x**2/288 - \
            43*x**4/10368 + O(x**5)

def test_issue402():
    x = Symbol("x")
    a = Symbol("a")
    e = x**(-2)*(x*sin(a + x) - x*sin(a))
    assert e.nseries(x, 0, 5) == cos(a) - sin(a)*x/2 - cos(a)*x**2/6 + \
            sin(a)*x**3/24 + O(x**4)
    e = x**(-2)*(x*cos(a + x) - x*cos(a))
    assert e.nseries(x, 0, 5) == -sin(a) - cos(a)*x/2 + sin(a)*x**2/6 + \
            cos(a)*x**3/24 + O(x**4)

def test_issue403():
    x = Symbol("x")
    e = sin(5*x)/sin(2*x)
    assert e.nseries(x, 0, 2) == Rational(5,2) + O(x)
    assert e.nseries(x, 0, 6) == Rational(5,2) - 35*x**2/4 + 329*x**4/48 + O(x**5)

def test_issue404():
    x = Symbol("x")
    e = sin(2 + x)/(2 + x)
    assert e.nseries(x, 0, 2) == sin(2)/2 + x*cos(2)/2 - x*sin(2)/4 + O(x**2)

def test_issue407():
    x = Symbol("x")
    e = (x + sin(3*x))**(-2)*(x*(x + sin(3*x)) - (x + sin(3*x))*sin(2*x))
    assert e.nseries(x, 0, 6) == -Rational(1,4) + 5*x**2/96 + 91*x**4/768 + O(x**5)

def test_issue409():
    x = Symbol("x", real=True)
    assert log(sin(x)).nseries(x, 0, 5) == log(x) - x**2/6 - x**4/180 + O(x**5)
    e = -log(x) + x*(-log(x) + log(sin(2*x))) + log(sin(2*x))
    assert e.nseries(x, 0, 5) == log(2)+log(2)*x-2*x**2/3-2*x**3/3-4*x**4/45+O(x**5)

def test_issue408():
    x = Symbol("x")
    e = x**(-4)*(x**2 - x**2*cos(x)**Rational(1,2))
    assert e.nseries(x, 0, 7) == Rational(1,4) + x**2/96 + 19*x**4/5760 + O(x**5)

def test_issue540():
    x = Symbol("x")
    assert sin(cos(x)).nseries(x, 0, 5) == sin(1) -x**2*cos(1)/2 - x**4*sin(1)/8 + x**4*cos(1)/24 + O(x**5)

def test_hyperbolic():
    x = Symbol("x")
    assert sinh(x).nseries(x, 0, 6) == x + x**3/6 + x**5/120 + O(x**6)
    assert cosh(x).nseries(x, 0, 5) == 1 + x**2/2 + x**4/24 + O(x**5)
    assert tanh(x).nseries(x, 0, 6) == x - x**3/3 + 2*x**5/15 + O(x**6)
    assert coth(x).nseries(x, 0, 6) == 1/x - x**3/45 + x/3 + 2*x**5/945 + O(x**6)
    assert asinh(x).nseries(x, 0, 6) == x - x**3/6 + 3*x**5/40 + O(x**6)
    assert acosh(x).nseries(x, 0, 6) == pi*I/2 - I*x - 3*I*x**5/40 - I*x**3/6 + O(x**6)
    assert atanh(x).nseries(x, 0, 6) == x + x**3/3 + x**5/5 + O(x**6)
    assert acoth(x).nseries(x, 0, 6) == x + x**3/3 + x**5/5 + pi*I/2 + O(x**6)

def test_series2():
    w = Symbol("w", real=True)
    x = Symbol("x", real=True)
    e =  w**(-2)*(w*exp(1/x - w) - w*exp(1/x))
    assert e.nseries(w, 0, 3) == -exp(1/x) + w * exp(1/x) / 2  + O(w**2)

def test_series3():
    w = Symbol("w", real=True)
    x = Symbol("x", real=True)
    e = w**(-6)*(w**3*tan(w) - w**3*sin(w))
    assert e.nseries(w, 0, 5) == Integer(1)/2 + O(w**2)

def test_bug4():
    w = Symbol("w")
    x = Symbol("x")
    e = x/(w**4 + x**2*w**4 + 2*x*w**4)*w**4
    assert e.nseries(w, 0, 2) in [x/(1 + 2*x + x**2), 1/(1+x/2+1/x/2)/2, 1/x/(1 + 2/x + x**(-2))]

def test_bug5():
    w = Symbol("w")
    x = Symbol("x")
    e = (-log(w) + log(1 + w*log(x)))**(-2)*w**(-2)*((-log(w) + log(1 + \
        x*w))*(-log(w) + log(1 + w*log(x)))*w - x*(-log(w) + log(1 + \
            w*log(x)))*w)
    assert e.nseries(w, 0, 1) == x/w/log(w) + 1/w + O(1/log(w))
    assert e.nseries(w, 0, 2) == x/w/log(w) + 1/w - x/log(w) + 1/log(w)*log(x)\
            + x*log(x)/log(w)**2 + O(w/log(w))


def test_issue1016():
    x = Symbol("x")
    assert ( sin(x)/(1 - cos(x)) ).nseries(x, 0, 2) == O(1/x)
    assert ( sin(x)**2/(1 - cos(x)) ).nseries(x, 0, 2) == O(1, x)

def test_pole():
    x = Symbol("x")
    raises(PoleError, "sin(1/x).series(x, 0, 5)")
    raises(PoleError, "sin(1+1/x).series(x, 0, 5)")
    raises(PoleError, "(x*sin(1/x)).series(x, 0, 5)")

def test_expsinbug():
    x = Symbol("x")
    assert exp(sin(x)).series(x, 0, 0) == O(1, x)
    assert exp(sin(x)).series(x, 0, 1) == 1+O(x)
    assert exp(sin(x)).series(x, 0, 2) == 1+x+O(x**2)
    assert exp(sin(x)).series(x, 0, 3) == 1+x+x**2/2+O(x**3)
    assert exp(sin(x)).series(x, 0, 4) == 1+x+x**2/2+O(x**4)
    assert exp(sin(x)).series(x, 0, 5) == 1+x+x**2/2-x**4/8+O(x**5)

def test_floor():
    x = Symbol('x')
    assert floor(x).series(x) == 0
    assert floor(-x).series(x) == -1
    assert floor(sin(x)).series(x) == 0
    assert floor(sin(-x)).series(x) == -1
    assert floor(x**3).series(x) == 0
    assert floor(-x**3).series(x) == -1
    assert floor(cos(x)).series(x) == 0
    assert floor(cos(-x)).series(x) == 0
    assert floor(5+sin(x)).series(x) == 5
    assert floor(5+sin(-x)).series(x) == 4

    assert floor(x).series(x, 2) == 2
    assert floor(-x).series(x, 2) == -3

    x = Symbol('x', negative=True)
    assert floor(x+1.5).series(x) == 1

def test_ceiling():
    x = Symbol('x')
    assert ceiling(x).series(x) == 1
    assert ceiling(-x).series(x) == 0
    assert ceiling(sin(x)).series(x) == 1
    assert ceiling(sin(-x)).series(x) == 0
    assert ceiling(1-cos(x)).series(x) == 1
    assert ceiling(1-cos(-x)).series(x) == 1
    assert ceiling(x).series(x, 2) == 3
    assert ceiling(-x).series(x, 2) == -2

def test_abs():
    x = Symbol('x')
    assert abs(x).nseries(x, 0, 4) == x
    assert abs(-x).nseries(x, 0, 4) == x
    assert abs(x+1).nseries(x, 0, 4) == x+1
    assert abs(sin(x)).nseries(x, 0, 4) == x - Rational(1, 6)*x**3 + O(x**4)
    assert abs(sin(-x)).nseries(x, 0, 4) == x - Rational(1, 6)*x**3 + O(x**4)

def test_dir():
    x = Symbol('x')
    y = Symbol('y')
    assert abs(x).series(x, 0, dir="+") == x
    assert abs(x).series(x, 0, dir="-") == -x
    assert floor(x+2).series(x,0,dir='+') == 2
    assert floor(x+2).series(x,0,dir='-') == 1
    assert floor(x+2.2).series(x,0,dir='-') == 2
    assert sin(x+y).series(x,0,dir='-') == sin(x+y).series(x,0,dir='+')

def test_issue405():
    a = Symbol("a")
    e = asin(a*x)/x
    assert e.series(x, 4) == a + a**3*x**2/6 + 3*a**5*x**4/40 + O(x**5)

def test_issue1342():
    x, a, b = symbols('x a b')
    f = 1/(1+a*x)
    assert f.series(x, 0, 5) == 1 - a*x + a**2*x**2 - a**3*x**3 + \
            a**4*x**4 + O(x**5)
    f = 1/(1+(a+b)*x)
    assert f.series(x, 0, 3) == 1 - a*x - b*x + a**2*x**2 + b**2*x**2 + \
            2*a*b*x**2 + O(x**3)
