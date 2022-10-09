import Mt.Task
import Mt.System

/-!
  # Mt: Reasoning about multithreaded algorithms
  This framework allows reasoning about multithreaded algorithms.
  Both blocking and non blocking algorithms are supported.

  We provide types to describe systems as a list of threads
  and to describe threads using monadic code. The fundamental
  monad `Mt.TaskM` allows side effects like modifying shared
  memory.

  The fundamental goal is to reason about multithreaded systems
  by decoupling the threads from each other. We reformulate the
  problem in a way such that it is to possible to reason about
  one thread at a time, almost as in the single threaded case.

  Basic idea: To decouple threads from each other, we have to
  specify some rules. We have to prove that all threads follow
  those rules, but we can do this one thread at a time, line by
  line. After each atomic step, the other threads may become active
  and change the shared memory. But they follow the same rules,
  and we do not need to know anything else about them. We have
  to assume that any of the allowed modifications has happened,
  but if we still succeed in proving our goal, our thread behaves
  correctly completly independent of the implementation of the
  other threads.

  ### High level overview
  * `Mt.TaskM`: A monad to represent single threaded code which
    can be iterated one time step at a time. There are primitives
    for atomic operations like read-modify or assertions.
  * `Mt.Thread`: Represents a single thread. It provides
    - the code to be executed (see `Mt.TaskM`)
    - a blocking predicate: The thread will sleep until this
      predicates returns `true`
    - thread local reservations (see `Mt.IsReservation`)
  * `Mt.System`: Represents a system consisting of
    - the shared state (shared memory) used by all threads
    - a list of active threads
    - a counter how many threads have paniced
  * `Mt.Spec`: The specification precisely specify the
    context and the required behaviour for threads. For example,
    it describes the type of the shared memory for threads and
    the invariants which all threads must enforce. Only threads
    with the same specification can be run in parallel.
  * `Mt.Reservation`: Reservations are thread local guarantees
    that must be considered by all threads. An active thread
    may create, modify or drop its reservations as long as the
    resulting state does not violate the specification.
    Examples:
    - Mutex. Only one thread a time may "reserve" it.
    - Semaphore. Only a limited number of threads may have
      a reservation for this semaphore.
    - Lower bound on a number in the shared memory. This
      effectly enforces the rule that this number must never be
      decreased by a thread, because another thread may have
      reserved a lower bound on it which could be broken.
  * `Mt.System.fundamental_validation_theorem`: The main theorem
    provided by this framework. It allows the decoupling of the
    threads. It states that a system is valid if:
    - it is valid at the current moment, i.e. the initial state
      is valid
    - all of its threads are valid (see `Mt.Thread.valid`)
-/