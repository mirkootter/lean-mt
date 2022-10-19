# Framework for reasoning about parallel algorithms
API Documentation: https://mirkootter.github.io/lean-mt-doc////Mt.html

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/mirkootter/lean-mt)

## Motivation
Multithreaded algorithms can be very hard to reason about. For simple problems, many developers are able to somehow "see" that the code is correct, but precise argumentation or even formal proofs are much more difficult, even for the simplest of problems.
#### Sample 1
Let us consider the following very simple example
```typescript
let x : atomic<int> = 0; // Assuming sequential consistency
let y : atomic<int> = 0; // Assuming sequential consistency

function thread1() {
  ++x;            // atomic increment
  ++y;            // atomic increment
  const py = y;   // atomic read
  const px = x;   // atomic read
  assert(px ≥ py);
}
```
The above code is correct: Spawning a (reasonable) number of those threads in parallel will never panic. Obviously, spawning several billion of those threads might panic due to new cases introduced by integer overflow.
#### Sample 2
We can make the sample above a little more complicated by adding a second type of thread. It is supposed to be spawned alongside `thread1`
```typescript
function thread2() {
  ++x;
  ++x;
  ++y;
  ++x;
  ++y;
  ++y;
  const py = y;   // atomic read
  const px = x;   // atomic read
  assert(px ≥ py);
}
```
We can spawn any number of `thread1` and `thread2` and none of them will panic (again, ignoring integer overflows for now)
#### Reasoning
Assuming sequential consistency, `thread1` can be cut intro 5 steps and interleaved with the steps of all other threads. If we spawn this method one time, we have exactly one possible combination. If we spawn it two times, we have

$${10 \choose 5}=252$$

combinations. If we spawn it three times, we have 756,756 combinations. For four threads, we get already 11,732,745,024 combinations. If we use also `thread2`, it gets even worse. Obviously, naive cases analysis is not a good idea.
## This project
We provide a powerful and easy to use framework using [Lean 4](https://leanprover.github.io/). Assuming the sequential consistent memory model, we follow the intuitive model of treating threads as iterable systems. In each time step, one thread is chosen and iterated. One iteration corresponds to one atomic operation.
We develop a system based on invariants: Designing some rules, we use the following simple idea:

> If all threads are following the same rules, we can focus our reasoning on one thread at a time. We have to prove that the current thread respects the rules, assuming the other threads do the same.

This idea is formalized. We develop a very general type of invariant and provide tools to specify threads and reason about them. We provide a central soundness theorem to justify the intuition above: Given any number of threads which respects a given invariant, the whole system will respect it.

## Reservations

Reservations are our way to reason about the thread's past
actions without needing to manage its full history. Often, we find
situations that a given thread may perform a certain action
only if he has performed a different action first.

Consider the line `++y` in `thread1`. This line is only sound
because the thread has called `++x` before.

This poses an additional challenge for writing thread specifications.
Without the line `++y`, we could simply demand that `x ≥ y` holds
at all time and use a simple inductive argument (induction over time).
However, the knowledge that a previous thread only ensured `x ≥ y`
is not enough to reason that `++y` is an allowed operation. We need
the stronger guarantee `x ≥ y + 1` for that.

Our solution to this problems are *reservations*. Reservations
are a certain kind of thread local variables. Since they are
thread local, they cannot be modifed by other threads. However,
the specification may demand certain properties of the
reservations which we can use as foundation for reasoning.

Going back to our example, we follow the intuitive approach
that `++x` creates some "luft" between `x` and `y` to prepare
`++y`. This luft is stored as reservation. The next time this
thread becomes active, the reservation will still be valid
and we conclude `y ≥ x + 1`.

Have a look at our revised example, which is much easier to
reason about:
```typescript
let x : atomic<int> = 0;
let y : atomic<int> = 0;

[@threadlocal] let luft : uint = 0;

void thread1b() {
  atomic { ++x; luft = 1; }
  atomic { ++y; luft = 0; }

  // ...
}
```
Using the invariant 

$$x\geq y+\sum_{t\in\mathrm{threads}}t.luft$$

we can now use a simple inductive approach to reason that
we have indeed `x ≥ y` at all times.

Note that we have omitted the assertion in the code above. This is
because the reservation above is not enough to prove that the
assertion will succeed. We read `x` and `y` at different points in
time. To reason about that, we need a second reservation:
```typescript
let x : atomic<int> = 0;
let y : atomic<int> = 0;

[@threadlocal] let luft  : uint = 0;
[@threadlocal] let min_x : int  = 0;

void thread1b() {
  atomic { ++x; luft = 1; }
  atomic { ++y; luft = 0; }

  const py = atomic { min_x = y ; y }
  const px = y;
  
  assert (px ≥ py);
}
```
with the two invariants

$$
  \left(x\geq y+\sum_{t\in\mathrm{threads}}t.luft\right)
  \quad\land\quad
  \forall {t\in\mathrm{threads}},\ x\geq t.min_x
$$

In fact, we can remove the $\forall$ operator:

$$
  \left(x\geq y+\sum_{t\in\mathrm{threads}}t.luft\right)
  \quad\land\quad
  \left(x\geq \underset{t\in\mathrm{threads}}\max\ t.min_x\right)
$$

Using this form, we can combine both reservations into one reservation
$R\in\mathbb{N}\times\mathbb{Z}$ to obtain the invariant

$$x\geq y+R.luft\quad\land\quad x\geq R.min_x$$

with $R:=\sum_{t\in\mathrm{threads}}R_t$ and the addition operator

$$
  \left(\begin{array}{c}luft\\min_x\end{array}\right)
  +\left(\begin{array}{c}luft'\\min_x'\end{array}\right)
  :=
  \left(\begin{array}{c}
    luft+luft'\\
    \max\ \{min_x,\ min_x'\}
  \end{array}\right)
$$

Note that the operator $+$ is both associative and commutative,
similar to the normal addition operator. We require an addition
operator with both properties for all reservations:

### Combining reservations

For our reasoning framework, we want to decouple threads from
each other as much as possible. We want to focus on one given
thread at a time, and refer to everything outside as "the environment".

It should not matter how many other threads they are. Only what
they do (or could do, potentially). If each of the other threads
has made reservations which we need to respect, it should not
matter whether one very complex threads has done a huge reservation
or if there are thousands of threads out there.

Additionally, it is reasonable to assume that the order of the
reservations does not matter, since the other threads could be
called in any order. In general, this assumption should not be
a problem. On the other hand, it greatly simplifies the framework:
We only have to reason about two reservations at a time: The
reservation of the environment, and the reservation of our own thread.
We can change our own reservation, but we have no control at all about
the reservation of the environment.

## The specification

Our main goal is to reason about a multithreaded system by
decoupling the threads from each other. Reasoning about the system
becomes reasoning about one thread at a time, even one line at a time.

To do that, we know that after each iteration the situation may have
completely changed. If the other threads may do virtually everything,
we would not be able to reason about anything. That's what the
specification is for. It describes precisely what a thread can do
and what not. If all threads of a given system follow the same
specification, we can use this information for reasoning.

In this project, the specification provides (among other things)
the following:
* The type `State` which represents the shared memory
* The type `Reservation` which represents the threadlocal reservations
* A validation predicate `Reservation → State → Prop`. For a valid
  system, this predicate must hold at all times
