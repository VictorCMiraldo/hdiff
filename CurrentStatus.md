# Design Space

After Paris, we decided that 
...

# Discussion on Sharing and Patch Optimality

## Losing Sharing

At first, our algorithm would cease to share too early.
For example, consider the trees A and B shown below:

```
a = bin (bin t u) k
b = bin (bin t u) t
```

The generation 1 algo, `diff-old a b` would return:

```
bin 0 k |-> bin 0 t
```

And we would lose the information about t being shared within
the metavariable 0. Although not an immediate issue, there are two
reasons for chosing against this behaviour:

1. In practice, we might often see changes that
   look like:
    
   > x := 42;    | x := 42;
   > ...         | ...
   > f(x + 5);   | g(x + 6);

   In which case, we'd like to keep track of the fact that x is shared. 

2. In theory, this definition can be justified by saying that
the `diff-old` function returns the patch with the largest domain
and no unused metavariables. Yet, the _unused metavar_ restriction 
feels artificial. Moreover, removing that restriction would make the notion 
of best patch crumble. With unused variables, the best patch between x and
y will always be `_ |-> y`

## A Better Story

In order to capture the idea that `(bin t u)` shouldn't be shared,
we define the notion of a _proper share_. In our case, `(bin t u)`
is a common subtree but not a proper share, for `t` has an occurence `b`
that happens _outside_ `(bin t u)`. 

Defn. _Proper Share_
> A common subtree `t` of two trees `x` and `y` is said to be
> a _proper share_ when there exists no subtree `k` of `t` such
> that `k` occurs in `x` or `y` in a place where it is not
> a subtree of `t` itself.

Naturally, all subtrees of a proper share are also proper shares. For this
reason, we are only interested in identifying as copies the _maximal proper shares_.

Defn. _Maximal Proper Share_
> A proper share `t` of `x` and `y` is said to be _maximal_ if
> there exists no other proper share `u` of `x` and `y` such that
> `t` is a subtree of `u`.

The algorithm that identifies the proper shares is simple. All we have to do
is record the arity of every subtree while hash-consing and annotate every subtree 
with the maximum arity of its subtrees. If the maximum arity of all its subtrees
is equal to its own arity, it is a proper share. 

Hence, `diff a b` now returns:

```
bin (bin 0 1) k |-> bin (bin 0 1) 0
```

### A Pratical Concern

This new specification will trigger our algorithm to share, in general, smaller trees
further from the root than what `diff-old` would. In practice, this can be too much.
Which suggest that we'd like to have some sort of configurable sharing control.
For exmaple, _don't share statemetns across functions_.

There is a naive way of implementing this, which works most of the time but shows
very erratic behavior when renaming functions, for example. This naive implementation
is done by changing the hash-consing. When computing the hash of a tree that is seen
inside a function, we can append the name of the function it is seen inside of.

```
def funct(x , y):   | def funct(x , y):
  do_smthing(x)     |   do_smthing(x)
  do_other(y)       |   do_other(y + 5)
                    |
def main():         | def main():
  x = 42            |   x = 46
  do_smthing(x)     |   do_smthing(x)
```

Although `do_smthing(x)` appears inside both `funct` and `main`, in this naive implementation
the oracle would have computed the hash of that statement differntly, and this would make it 
so that we'd see two different metaraviables as a patch:

```
def funct(x , y):   | def funct(x , y):
  0                 |   0
  do_other(y)       |   do_other(y + 5)
                    |
def main():         | def main():
  x = 42            |   x = 46
  1                 |   1
```

The erratic behavior occurs when we rename a function:

```
def funct(x , y):   | def newname(x , y):
  do_smthing(x)     |   do_smthing(x)
  do_other(y)       |   do_other(y)
```

Now, no statement from the body will be detected as _shareable_ since they received different
hashes in both source and destination. This is a pretty big issue and I have no good
way around this for the moment.

# Relation to Edit Scripts

There are a number of flavours of edit scripts. Every author likes to consider
a slightly different set of operations. The tree-edit-distance community
usually considers insertions, deletions, relabeling and copies.
In a typed world, relabeling is impossible in general, as two different constructors
will generally have two different types, and hence, the people on the typed
world consider insertions, deletions and copies only. We will distinguish them
by refereing to _IDRC-edit-scripts_ versus _IDC-edit-scripts_ when necessary. If nothing
is said, we mean _IDC-edit-scripts_.

The cost of an _IDC-edit-script_ is given by the number of insertions and deletions.
Which is essentially a count of the constructor being deleted and inserted. The _best_
edit script is that with the lowest cost. The best edit script is not necessarily unique.

Translating a pattern-expression patch into _IDC-edit-scripts_ is possible, but
I'm not sure there exists a way of producing the _best_ such edit script. First
and foremost, we have to address the fact that edit scripts can't duplicate, contract
or permute subtrees. Therefore, take the patch:

```
bin (bin 0 1) k |-> bin (bin 0 1) 0
```

A preorder traversal of the deletion context gives variables `[0,1]`,
and in the insertion context we have `[0,1,0]`. In order to decide which variables to
_not copy_, we can compute a longest common subsequence of `[0,1]` and `[0,1,0]`,
which instructs us to _forget about_ the last occurence of 0, because
an edit script wouldn't be able to represent it anyway. Now, our patch becomes:

```
bin (bin 0 1) k |-> bin (bin 0 1) t
```

Now we have a patch where variables are not permuted, contracted or duplicated.
This enables us to traverse the deletion context, issuing one `del` operation until we
reach a variable:

```
del bin

bin 0 1 , k |-> bin (bin 0 1) t
```

Then we switch to the insertion context, then deletion, then insertion...

```
del bin
ins bin
del bind
ins bin
0, 1 , k |-> 0 , 1 , t
```

And when we reach a variable on both sides we issue a copy.
Essentially, the variables act as a synchronization point.
For this reason, if we have multiple contractions and duplications,
we want to make sure to synchronize at the beginning of
contractions and at the end of duplications. For example:

```
bin k (bin 0 (bin a 1)) |-> bin 0 (bin 0 (bin a 1))
```

We want to make sure we get to copy the a, for that,
we must see that the syncpoint happens at the second
occurence of 0 in the deletion context. A great showcase
to this is:

```
git checkout da389ef
digem diff --show-es examples/While/MillerRabin/MillerRabin{1,2}.while
```

Now lets look at what happens on the classic swap patch:

```
bin 0 1 |-> bin 1 0
```

We will have to chose whether to copy `0` or `1`. If we compute the simple
lcs between `[0,1]` and `[1,0]`, we might choose the wrong one. Therefore,
we weight the choice by the size of the subtree that the metavariable is
matching. This way, we ensure to copy the most.

I'm still working on this. It seems like it would be better to interleave the insertion
and deletion bit one by one and if we insert and delete the same constructor we can just copy it
instead. This might produce a better edit script.

# Planned Experiments

1. Compare the result of producing an edit script from a pattern-exp patch
or computing it directly. How close to the optimal can we get? Can we prove
optimilaity if we see it consistently?

2. Since the cost of an edit-script is the number of constructors
it deletes plus the number of constructors it inserts, we can do this count
directly on a pattern-exp patch and see how they relate. 

3. Understand how many duplications we see in practice and the number of
variables that are duplicated on our real dataset. Maybe all of this sharing-control
work is useless.


