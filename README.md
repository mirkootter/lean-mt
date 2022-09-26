# Framework for reasoning about parallel algorithms
**Important** This project is in very early stages
## Motivation
Multithreaded algorithms can be very hard to reason about. For simple problems, many developers are able to somehow "see" that the code is correct, but precise argumentation or even formal proofs are much more difficult, even for the simplest of problems.
#### Sample 1
Let us consider the following very simple example
```typescript
let x : atomic<int> = 0; // Assuming sequential consistency
let y : atmoic<int> = 0; // Assuming sequential consistency

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
