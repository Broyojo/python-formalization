import PyLean.Registry
import PyLean.CoreLibs.Misc.Diff
import PyLean.CoreLibs.Misc.Graphlib.Props
import PyLean.CoreLibs.Misc.Graphlib.Total
import PyLean.CoreLibs.Misc.Sched.Props
import PyLean.CoreLibs.Misc.Queue.Props
import PyLean.CoreLibs.Misc.Numbers.Props
import PyLean.CoreLibs.Misc.Types.Props
import PyLean.CoreLibs.Misc.Contextlib.Props
import PyLean.CoreLibs.Misc.Contextlib.StackProps
import PyLean.CoreLibs.Misc.Weakref.Props2

/-! Registry for the `Misc` area of CoreLibs: Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py, CPython 3.15.2. -/

namespace PyLean.CoreLibs.Misc

open PyLean.Registry

def graphlibEntries : List Entry := [
  { id := "misc-graphlib-add-invariant", pyFile := "Lib/graphlib.py"
    pyFns := ["_NodeInfo.__init__", "TopologicalSorter.__init__", "TopologicalSorter._get_nodeinfo",
              "TopologicalSorter.add"]
    statement := "For every sorter built by __init__ and add, node keys are distinct, every successor is a node, and npredecessors is the number of occurrences of the node in the successor lists."
    source := "comment Lib/graphlib.py:16-22"
    status := .proven, prop := ``Graphlib.AddInvariant, thm := some ``Graphlib.addInvariant_proven },
  { id := "misc-graphlib-prepare-guards", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter.get_ready", "TopologicalSorter.is_active",
              "TopologicalSorter.__bool__", "TopologicalSorter.done", "TopologicalSorter.add"]
    statement := "Before prepare, get_ready, is_active, __bool__ and done raise ValueError and change nothing; after prepare, add raises ValueError."
    source := "docstrings of TopologicalSorter"
    status := .proven, prop := ``Graphlib.PrepareGuards, thm := some ``Graphlib.prepareGuards_proven },
  { id := "misc-graphlib-prepare-cases", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter.prepare"]
    statement := "prepare raises ValueError once nodes are passed out, succeeds with nothing changed when repeated, and with a cycle raises CycleError with _ready_nodes already set."
    source := "docstring of prepare, comment Lib/graphlib.py:104-107"
    status := .proven, prop := ``Graphlib.PrepareCases, thm := some ``Graphlib.prepareCases_proven },
  { id := "misc-graphlib-done-validation", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter.done"]
    statement := "done raises the documented ValueError for a node not added, one not passed out, and one already done, and the state invariant leaves no other status, so the assert cannot fire."
    source := "docstring of done"
    status := .proven, prop := ``Graphlib.DoneValidation, thm := some ``Graphlib.doneValidation_proven },
  { id := "misc-graphlib-active-ready", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter.is_active", "TopologicalSorter.__bool__", "TopologicalSorter.get_ready"]
    statement := "is_active is true exactly when a passed-out node is not done or a node is ready; __bool__ equals it; get_ready hands out each ready node once."
    source := "docstrings of is_active, get_ready"
    status := .proven, prop := ``Graphlib.ActiveReady, thm := some ``Graphlib.activeReady_proven },
  { id := "misc-graphlib-find-cycle-sound", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter._find_cycle"]
    statement := "A list returned by _find_cycle has length >= 2, equal first and last elements, and each element is an immediate predecessor of the next."
    source := "docstring of CycleError"
    status := .proven, prop := ``Graphlib.FindCycleSound, thm := some ``Graphlib.findCycleSound_proven },
  { id := "misc-graphlib-no-report-no-cycle", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter._find_cycle"]
    statement := "When _find_cycle returns None the graph has no closed path."
    source := "docstring of prepare"
    status := .proven, prop := ``Graphlib.NoReportNoCycle, thm := some ``Graphlib.noReportNoCycle_proven },
  { id := "misc-graphlib-find-cycle-total", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter._find_cycle"]
    statement := "_find_cycle ends on every graph built by __init__ and add."
    source := "invariant: no hang"
    status := .proven, prop := ``Graphlib.FindCycleTotal, thm := some ``Graphlib.findCycleTotal_proven },
  { id := "misc-graphlib-static-order", pyFile := "Lib/graphlib.py"
    pyFns := ["TopologicalSorter.static_order", "TopologicalSorter.prepare",
              "TopologicalSorter.get_ready", "TopologicalSorter.done",
              "TopologicalSorter.is_active", "TopologicalSorter._find_cycle"]
    statement := "For every graph built with __init__ and add: without a cycle static_order lists every node exactly once with each predecessor first, and the loop cannot fail; with a cycle it raises CycleError."
    source := "docstring of static_order"
    status := .proven, prop := ``Graphlib.StaticOrderTopological,
    thm := some ``Graphlib.staticOrderTopological_proven }
]

def schedEntries : List Entry := [
  { id := "misc-sched-queue-ordered", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.__init__", "scheduler.enterabs", "scheduler.enter", "scheduler.cancel",
              "scheduler.queue"]
    statement := "With totally ordered times and priorities, for every state reached through enterabs, enter and cancel, queue lists each queued event once in (time, priority, sequence) order."
    source := "docstrings of scheduler.queue, Event.priority, Event.sequence"
    status := .proven, prop := ``Sched.QueueOrdered, thm := some ``Sched.queueOrdered_proven },
  { id := "misc-sched-enter-relative", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.enter"]
    statement := "enter reads the clock once and is enterabs at timefunc() + delay; a failure of the clock or of + leaves the queue."
    source := "docstring of enter"
    status := .proven, prop := ``Sched.EnterRelative, thm := some ``Sched.enterRelative_proven },
  { id := "misc-sched-enterabs-id", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.enterabs"]
    statement := "enterabs returns the event with its arguments and the old counter as sequence, kwargs defaults to {}, the counter advances, and the queue gains exactly that event."
    source := "docstring of enterabs"
    status := .proven, prop := ``Sched.EnterabsId, thm := some ``Sched.enterabsId_proven },
  { id := "misc-sched-empty", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.empty"]
    statement := "empty() is True exactly when queue is []."
    source := "docstring of empty"
    status := .proven, prop := ``Sched.EmptyQueue, thm := some ``Sched.emptyQueue_proven },
  { id := "misc-sched-cancel-absent", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.cancel"]
    statement := "cancel of an event not in the queue raises ValueError and changes nothing."
    source := "docstring of cancel"
    status := .proven, prop := ``Sched.CancelAbsent, thm := some ``Sched.cancelAbsent_proven },
  { id := "misc-sched-cancel-present", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.cancel"]
    statement := "cancel of a queued event, with sequence numbers distinct as enterabs makes them, removes it and only it and leaves a heap."
    source := "docstring of cancel"
    status := .proven, prop := ``Sched.CancelPresent, thm := some ``Sched.cancelPresent_proven },
  { id := "misc-sched-run-basics", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.run"]
    statement := "run on an empty queue returns None without reading the clock; with blocking false and the first event in the future it returns the delay and leaves the queue."
    source := "docstring of run"
    status := .proven, prop := ``Sched.RunBasics, thm := some ``Sched.runBasics_proven },
  { id := "misc-sched-run-action-raises", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.run"]
    statement := "An action that raises propagates; its event has left the queue and the others remain, so run may be called again."
    source := "docstring of run"
    status := .proven, prop := ``Sched.RunActionRaises, thm := some ``Sched.runActionRaises_proven },
  { id := "misc-sched-run-order", pyFile := "Lib/sched.py"
    pyFns := ["scheduler.run"]
    statement := "With every event due and actions that only record themselves, run empties the queue, calls the actions in the order queue lists them, and returns None."
    source := "docstring of run"
    status := .proven, prop := ``Sched.RunOrder, thm := some ``Sched.runOrder_proven }
]

def queueEntries : List Entry := [
  { id := "misc-queue-fifo", pyFile := "Lib/queue.py"
    pyFns := ["Queue.__init__", "Queue._init", "Queue._qsize", "Queue._put", "Queue._get",
              "Queue.put", "Queue.get", "Queue.put_nowait", "Queue.get_nowait"]
    statement := "From a new Queue, put_nowait of items that fit succeeds, unfinished_tasks counts them, and get_nowait returns them in the same order."
    source := "docstring of Queue, Doc/library/queue.rst"
    status := .proven, prop := ``Queue.QueueFifoOrder, thm := some ``Queue.queueFifoOrder_proven },
  { id := "misc-queue-lifo", pyFile := "Lib/queue.py"
    pyFns := ["LifoQueue._init", "LifoQueue._qsize", "LifoQueue._put", "LifoQueue._get"]
    statement := "LifoQueue returns the items reversed."
    source := "docstring of LifoQueue"
    status := .proven, prop := ``Queue.LifoQueueOrder, thm := some ``Queue.lifoQueueOrder_proven },
  { id := "misc-queue-priority", pyFile := "Lib/queue.py"
    pyFns := ["PriorityQueue._init", "PriorityQueue._qsize", "PriorityQueue._put", "PriorityQueue._get"]
    statement := "When < on the items is a strict weak order that raises nothing, PriorityQueue returns a permutation of the items, lowest first."
    source := "docstring of PriorityQueue"
    status := .proven, prop := ``Queue.PriorityQueueOrder, thm := some ``Queue.priorityQueueOrder_proven },
  { id := "misc-queue-failed-put", pyFile := "Lib/queue.py"
    pyFns := ["PriorityQueue._put", "Queue.put"]
    statement := "A put whose heappush raises does not count in unfinished_tasks, and the item stays at the end of queue, as heappush appends first."
    source := "invariant; rollback declined in python/cpython#100968, so the behaviour is stated"
    status := .proven, prop := ``Queue.FailedPutKeepsItem, thm := some ``Queue.failedPutKeepsItem_proven },
  { id := "misc-queue-nowait-boundary", pyFile := "Lib/queue.py"
    pyFns := ["Queue.put_nowait", "Queue.get_nowait", "Queue.put", "Queue.get"]
    statement := "For every queue organization: ShutDown first, Full exactly when 0 < maxsize <= qsize(), Empty exactly when qsize() == 0, leaving the queue unchanged."
    source := "docstrings of put, get"
    status := .proven, prop := ``Queue.NowaitBoundary, thm := some ``Queue.nowaitBoundary_proven },
  { id := "misc-queue-size-predicates", pyFile := "Lib/queue.py"
    pyFns := ["Queue.qsize", "Queue.empty", "Queue.full"]
    statement := "empty() is qsize() == 0 and full() is 0 < maxsize <= qsize()."
    source := "docstrings of empty, full"
    status := .proven, prop := ``Queue.SizePredicates, thm := some ``Queue.sizePredicates_proven },
  { id := "misc-queue-task-accounting", pyFile := "Lib/queue.py"
    pyFns := ["Queue.task_done", "Queue.join"]
    statement := "task_done decrements while the count is positive and raises ValueError at 0; join returns exactly when the count is 0; put raises the count and get leaves it."
    source := "docstrings of task_done, join"
    status := .proven, prop := ``Queue.TaskAccounting, thm := some ``Queue.taskAccounting_proven },
  { id := "misc-queue-timeout-validation", pyFile := "Lib/queue.py"
    pyFns := ["Queue.put", "Queue.get"]
    statement := "A negative timeout with block raises ValueError on a bounded put and on any get; an unbounded put ignores it, and block=False ignores it."
    source := "docstrings of put, get"
    status := .proven, prop := ``Queue.TimeoutValidation, thm := some ``Queue.timeoutValidation_proven },
  { id := "misc-queue-timed-outcome", pyFile := "Lib/queue.py"
    pyFns := ["Queue.put", "Queue.get"]
    statement := "A timed put on a full queue raises Full and a timed get on an empty queue raises Empty, after timeout has passed, with the queue unchanged."
    source := "docstrings of put, get"
    status := .proven, prop := ``Queue.TimedOutcome, thm := some ``Queue.timedOutcome_proven },
  { id := "misc-queue-shutdown", pyFile := "Lib/queue.py"
    pyFns := ["Queue.shutdown"]
    statement := "After shutdown put raises ShutDown; get drains what is queued and then raises ShutDown; immediate=True empties the queue and lowers unfinished_tasks by the number removed, not below 0."
    source := "docstring of shutdown"
    status := .proven, prop := ``Queue.ShutdownSemantics, thm := some ``Queue.shutdownSemantics_proven },
  { id := "misc-simplequeue-twins-blocking", pyFile := "Lib/queue.py"
    pyFns := ["_PySimpleQueue.__init__", "_PySimpleQueue.put", "_PySimpleQueue.get",
              "_PySimpleQueue.put_nowait", "_PySimpleQueue.get_nowait", "_PySimpleQueue.empty",
              "_PySimpleQueue.qsize"]
    statement := "Without a timeout combined with block=False, _PySimpleQueue and _queue.SimpleQueue give the same results and contents."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .proven, prop := ``Queue.SimpleQueueTwinsBlocking,
    thm := some ``Queue.simpleQueueTwinsBlocking_proven },
  { id := "misc-simplequeue-twins", pyFile := "Lib/queue.py"
    pyFns := ["_PySimpleQueue.get"]
    statement := "_PySimpleQueue.get and _queue.SimpleQueue.get agree for all arguments: with block false both ignore timeout."
    source := "docstring of _PySimpleQueue.get: timeout is ignored when block is false"
    status := .proven, prop := ``Queue.SimpleQueueGetTwins, thm := some ``Queue.simpleQueueGetTwins_proven
    notes := "python/cpython#156476 is fixed in 3.15.2; the old record is corelibs-pysimplequeue-nonblocking-timeout." }
]

def numbersEntries : List Entry := [
  { id := "misc-numbers-sub-rsub", pyFile := "Lib/numbers.py"
    pyFns := ["Complex.__sub__", "Complex.__rsub__"]
    statement := "For every subclass whose + and unary - implement an abelian group, __sub__ is x + (-y) and __rsub__ is y + (-x)."
    source := "docstrings of __sub__, __rsub__"
    status := .proven, prop := ``Numbers.ComplexSubRsub, thm := some ``Numbers.complexSubRsub_proven },
  { id := "misc-numbers-sub-neg-first", pyFile := "Lib/numbers.py"
    pyFns := ["Complex.__sub__", "Complex.__rsub__"]
    statement := "__sub__ and __rsub__ evaluate unary - first: its exception is the result."
    source := "invariant"
    status := .proven, prop := ``Numbers.ComplexSubNegFirst, thm := some ``Numbers.complexSubNegFirst_proven },
  { id := "misc-numbers-bool", pyFile := "Lib/numbers.py"
    pyFns := ["Complex.__bool__"]
    statement := "When == is equality of values, bool(x) is x != 0."
    source := "docstring of __bool__"
    status := .proven, prop := ``Numbers.ComplexBool, thm := some ``Numbers.complexBool_proven },
  { id := "misc-numbers-divmod", pyFile := "Lib/numbers.py"
    pyFns := ["Real.__divmod__", "Real.__rdivmod__"]
    statement := "__rdivmod__(self, other) is __divmod__(other, self), and // is evaluated before %."
    source := "docstrings of __divmod__, __rdivmod__"
    status := .proven, prop := ``Numbers.RealDivmod, thm := some ``Numbers.realDivmod_proven },
  { id := "misc-numbers-divmod-euclid", pyFile := "Lib/numbers.py"
    pyFns := ["Real.__divmod__"]
    statement := "Over the ints with Python's // and %, the pair from __divmod__ satisfies q * b + r = a for b != 0."
    source := "docstring of __divmod__"
    status := .proven, prop := ``Numbers.RealDivmodEuclid, thm := some ``Numbers.realDivmodEuclid_proven },
  { id := "misc-numbers-real-components", pyFile := "Lib/numbers.py"
    pyFns := ["Real.real", "Real.imag", "Real.conjugate", "Real.__complex__"]
    statement := "real and conjugate agree and are the number when + is the identity, imag is 0, and complex(x) is (float(x), 0)."
    source := "docstrings of Real.real, imag, conjugate, __complex__"
    status := .proven, prop := ``Numbers.RealComponents, thm := some ``Numbers.realComponents_proven },
  { id := "misc-numbers-integral-rational", pyFile := "Lib/numbers.py"
    pyFns := ["Integral.__float__", "Integral.numerator", "Integral.denominator", "Integral.__index__",
              "Rational.__float__"]
    statement := "Rational.__float__ on the Integral properties gives Integral.__float__ whenever n / 1 is float(n), and __index__ is int(self)."
    source := "docstrings of Integral, Rational.__float__"
    status := .proven, prop := ``Numbers.IntegralRationalAgree, thm := some ``Numbers.integralRationalAgree_proven },
  { id := "misc-numbers-abstract-stubs", pyFile := "Lib/numbers.py"
    pyFns := []
    statement := "Every abstract method raises NotImplementedError for every argument, except Complex.__complex__, which returns None."
    source := "bodies of the abstract methods"
    status := .proven, prop := ``Numbers.AbstractStubs, thm := some ``Numbers.abstractStubs_proven },
  { id := "misc-numbers-mixin-over-stub", pyFile := "Lib/numbers.py"
    pyFns := ["Complex.__sub__", "Complex.__rsub__"]
    statement := "A mixin over a primitive that is still abstract raises NotImplementedError; it cannot return a wrong number."
    source := "invariant"
    status := .proven, prop := ``Numbers.MixinOverStub, thm := some ``Numbers.mixinOverStub_proven }
]

def keywordEntries : List Entry := [
  { id := "misc-keyword-lists", pyFile := "Lib/keyword.py"
    pyFns := ["iskeyword", "issoftkeyword"]
    statement := "kwlist and softkwlist are duplicate-free and disjoint, and iskeyword, issoftkeyword decide membership."
    source := "Lib/keyword.py, generated from Grammar/python.gram"
    status := .proven, prop := ``Keyword.KeywordLists, thm := some ``Keyword.keywordLists_proven }
]

def typesEntries : List Entry := [
  { id := "misc-types-resolve-bases-twin", pyFile := "Lib/types.py"
    pyFns := ["resolve_bases"]
    statement := "types.resolve_bases and update_bases in bltinmodule.c give the same result, exception and identity of the tuple, for every object model."
    source := "PEP 560, Doc/library/types.rst"
    status := .proven, prop := ``Types.ResolveBasesTwin, thm := some ``Types.resolveBasesTwin_proven },
  { id := "misc-types-resolve-bases-flat", pyFile := "Lib/types.py"
    pyFns := ["resolve_bases"]
    statement := "resolve_bases replaces each base with __mro_entries__ in place by the tuple it returns, keeps the others in order, and returns the original object exactly when no base has the method."
    source := "docstring of resolve_bases, PEP 560"
    status := .proven, prop := ``Types.ResolveBasesFlat, thm := some ``Types.resolveBasesFlat_proven },
  { id := "misc-types-calculate-meta", pyFile := "Lib/types.py"
    pyFns := ["_calculate_meta"]
    statement := "When issubclass is a preorder, _calculate_meta returns a subclass of the candidate and of every base's metaclass, or raises the metaclass conflict TypeError."
    source := "docstring of _calculate_meta"
    status := .proven, prop := ``Types.CalculateMetaWinner, thm := some ``Types.calculateMetaWinner_proven },
  { id := "misc-types-prepare-class-meta", pyFile := "Lib/types.py"
    pyFns := ["prepare_class"]
    statement := "A metaclass entry of kwds is removed and the other keywords stay in order."
    source := "docstring of prepare_class"
    status := .proven, prop := ``Types.PrepareClassMeta, thm := some ``Types.prepareClassMeta_proven },
  { id := "misc-types-prepare-class-default", pyFile := "Lib/types.py"
    pyFns := ["prepare_class"]
    statement := "Without metaclass and bases the candidate is type; a candidate that is no class skips _calculate_meta; __prepare__ is called with the remaining keywords."
    source := "docstring of prepare_class"
    status := .proven, prop := ``Types.PrepareClassDefault, thm := some ``Types.prepareClassDefault_proven },
  { id := "misc-types-new-class-orig-bases", pyFile := "Lib/types.py"
    pyFns := ["new_class"]
    statement := "__orig_bases__ is written, with the original bases, exactly when resolution changed the bases; the metaclass gets the resolved tuple and runs after exec_body."
    source := "docstring of new_class, PEP 560"
    status := .proven, prop := ``Types.NewClassOrigBases, thm := some ``Types.newClassOrigBases_proven },
  { id := "misc-types-get-original-bases", pyFile := "Lib/types.py"
    pyFns := ["get_original_bases"]
    statement := "get_original_bases returns __orig_bases__ from the class's own __dict__, else __bases__, and raises TypeError on anything else."
    source := "docstring of get_original_bases"
    status := .proven, prop := ``Types.GetOriginalBases, thm := some ``Types.getOriginalBases_proven },
  { id := "misc-types-dca-accessors", pyFile := "Lib/types.py"
    pyFns := ["DynamicClassAttribute.__init__", "DynamicClassAttribute.getter",
              "DynamicClassAttribute.setter", "DynamicClassAttribute.deleter"]
    statement := "getter, setter and deleter each replace one function and keep the others and overwrite_doc."
    source := "comment Lib/types.py:217"
    status := .proven, prop := ``Types.DcaAccessors, thm := some ``Types.dcaAccessors_proven },
  { id := "misc-types-dca-doc", pyFile := "Lib/types.py"
    pyFns := ["DynamicClassAttribute.__init__", "DynamicClassAttribute.getter"]
    statement := "An explicit truthy doc stays through getter; otherwise __doc__ is fget's and getter takes the new fget's."
    source := "comment Lib/types.py:217"
    status := .proven, prop := ``Types.DcaDoc, thm := some ``Types.dcaDoc_proven },
  { id := "misc-types-dca-descriptor", pyFile := "Lib/types.py"
    pyFns := ["DynamicClassAttribute.__get__", "DynamicClassAttribute.__set__",
              "DynamicClassAttribute.__delete__"]
    statement := "Class access raises AttributeError unless fget is abstract; instance access calls fget; a missing function raises AttributeError with the source's message."
    source := "docstring of DynamicClassAttribute"
    status := .proven, prop := ``Types.DcaDescriptor, thm := some ``Types.dcaDescriptor_proven },
  { id := "misc-types-generator-wrapper", pyFile := "Lib/types.py"
    pyFns := ["_GeneratorWrapper.__init__", "_GeneratorWrapper.send", "_GeneratorWrapper.throw",
              "_GeneratorWrapper.close", "_GeneratorWrapper.gi_code", "_GeneratorWrapper.gi_frame",
              "_GeneratorWrapper.gi_running", "_GeneratorWrapper.gi_yieldfrom",
              "_GeneratorWrapper.gi_suspended", "_GeneratorWrapper.__next__",
              "_GeneratorWrapper.__iter__"]
    statement := "For every wrapped object and operation sequence, results through _GeneratorWrapper are those of the object; __iter__ returns the generator exactly when it is a native one."
    source := "invariant"
    status := .proven, prop := ``Types.WrapperTransparent, thm := some ``Types.wrapperTransparent_proven },
  { id := "misc-types-generator-states", pyFile := "Lib/types.py"
    pyFns := ["_GeneratorWrapper.gi_state", "_GeneratorWrapper.cr_state"]
    statement := "gi_state is the state of the wrapped object and cr_state the same state in a coroutine's names, and a read that raises raises through both."
    source := "Lib/types.py:286-291"
    status := .proven, prop := ``Types.WrapperStates, thm := some ``Types.wrapperStates_proven },
  { id := "misc-types-coroutine", pyFile := "Lib/types.py"
    pyFns := ["coroutine"]
    statement := "coroutine rejects non-callables, returns coroutine functions as they are, adds CO_ITERABLE_COROUTINE to generator functions, and wraps the rest."
    source := "Doc/library/types.rst"
    status := .proven, prop := ``Types.CoroutineCases, thm := some ``Types.coroutineCases_proven },
  { id := "misc-types-coroutine-wrapped", pyFile := "Lib/types.py"
    pyFns := ["coroutine"]
    statement := "wrapped wraps exactly generators in the collections.abc sense that are no coroutines and no iterable coroutines."
    source := "comments Lib/types.py:341-351"
    status := .proven, prop := ``Types.WrappedDecision, thm := some ``Types.wrappedDecision_proven }
]

def contextlibEntries : List Entry := [
  { id := "misc-ctx-abstract-bases", pyFile := "Lib/contextlib.py"
    pyFns := ["AbstractContextManager.__enter__", "AbstractContextManager.__exit__",
              "AbstractContextManager.__subclasshook__", "AbstractAsyncContextManager.__aenter__",
              "AbstractAsyncContextManager.__aexit__", "AbstractAsyncContextManager.__subclasshook__"]
    statement := "__enter__ returns self, __exit__ returns None, and __subclasshook__ is True exactly when all methods are found with a non-None nearest definition, NotImplemented on a subclass."
    source := "docstrings of the ABCs"
    status := .proven, prop := ``Contextlib.AbstractBases, thm := some ``Contextlib.abstractBases_proven },
  { id := "misc-ctx-subclasshook-none", pyFile := "Lib/contextlib.py"
    pyFns := ["AbstractContextManager.__subclasshook__", "AbstractAsyncContextManager.__subclasshook__"]
    statement := "A None in the class body hides an inherited method from __subclasshook__."
    source := "Lib/_collections_abc.py:108-118"
    status := .proven, prop := ``Contextlib.SubclassHookNone, thm := some ``Contextlib.subclassHookNone_proven },
  { id := "misc-ctx-decorator", pyFile := "Lib/contextlib.py"
    pyFns := ["ContextDecorator._recreate_cm", "AsyncContextDecorator._recreate_cm"]
    statement := "_recreate_cm returns self and a decorated plain function is its body inside with self._recreate_cm(); a failing recreation does not run the function."
    source := "docstring of ContextDecorator"
    status := .proven, prop := ``Contextlib.DecoratorIsWith, thm := some ``Contextlib.decoratorIsWith_proven },
  { id := "misc-ctx-recreate", pyFile := "Lib/contextlib.py"
    pyFns := ["_GeneratorContextManagerBase.__init__", "_GeneratorContextManagerBase._recreate_cm",
              "contextmanager", "asynccontextmanager"]
    statement := "_recreate_cm makes a fresh manager while func is there and raises AttributeError after __enter__; __doc__ comes from func, else from the class."
    source := "comments Lib/contextlib.py:173, :123-125"
    status := .proven, prop := ``Contextlib.RecreateFresh, thm := some ``Contextlib.recreateFresh_proven },
  { id := "misc-ctx-enter", pyFile := "Lib/contextlib.py"
    pyFns := ["_GeneratorContextManager.__enter__", "_AsyncGeneratorContextManager.__aenter__"]
    statement := "__enter__ returns the yielded value, turns a stop into RuntimeError(\"generator didn't yield\"), lets other exceptions through, and is one-shot."
    source := "Lib/contextlib.py:198-205"
    status := .proven, prop := ``Contextlib.EnterCases, thm := some ``Contextlib.enterCases_proven },
  { id := "misc-ctx-exit-no-exception", pyFile := "Lib/contextlib.py"
    pyFns := ["_GeneratorContextManager.__exit__", "_AsyncGeneratorContextManager.__aexit__"]
    statement := "__exit__(None, None, None) gives False for a generator that ends, RuntimeError after close for one that yields, and passes other exceptions."
    source := "Lib/contextlib.py:208-217"
    status := .proven, prop := ``Contextlib.ExitNoException, thm := some ``Contextlib.exitNoException_proven },
  { id := "misc-ctx-exit-throw-cases", pyFile := "Lib/contextlib.py"
    pyFns := ["_GeneratorContextManager.__exit__", "_AsyncGeneratorContextManager.__aexit__"]
    statement := "For every generator, __exit__ with an exception does what the comments of the source say in each branch of throw: yield, stop, value back, wrapped value, other exception."
    source := "comments Lib/contextlib.py:226-254"
    status := .proven, prop := ``Contextlib.ExitThrowCases, thm := some ``Contextlib.exitThrowCases_proven },
  { id := "misc-ctx-exit-never-raises-value", pyFile := "Lib/contextlib.py"
    pyFns := ["_GeneratorContextManager.__exit__", "_AsyncGeneratorContextManager.__aexit__"]
    statement := "On every generator whose close() does not raise value, __exit__ never raises the exception passed in."
    source := "comment Lib/contextlib.py:249-254"
    status := .proven, prop := ``Contextlib.ExitNeverRaisesValue, thm := some ``Contextlib.exitNeverRaisesValue_proven },
  { id := "misc-ctx-try-finally", pyFile := "Lib/contextlib.py"
    pyFns := ["contextmanager", "asynccontextmanager", "_GeneratorContextManager.__enter__",
              "_GeneratorContextManager.__exit__"]
    statement := "With a generator that yields once and finishes, the with statement behaves as the try/finally of the docstring: the body's value, or the same exception object."
    source := "docstring of contextmanager"
    status := .proven, prop := ``Contextlib.ContextmanagerTryFinally,
    thm := some ``Contextlib.contextmanagerTryFinally_proven },
  { id := "misc-ctx-async-twin", pyFile := "Lib/contextlib.py"
    pyFns := ["_AsyncGeneratorContextManager.__aexit__", "_GeneratorContextManager.__exit__"]
    statement := "When neither value nor the raised exception is a stop exception, __aexit__ and __exit__ give the same result on the same generator behaviour."
    source := "invariant: sync and async siblings"
    status := .proven, prop := ``Contextlib.AsyncTwinExit, thm := some ``Contextlib.asyncTwinExit_proven },
  { id := "misc-ctx-closing", pyFile := "Lib/contextlib.py"
    pyFns := ["closing.__init__", "closing.__enter__", "closing.__exit__", "aclosing.__init__",
              "aclosing.__aenter__", "aclosing.__aexit__"]
    statement := "with closing(x) binds x, calls close exactly once whatever the body does, and suppresses nothing."
    source := "docstring of closing"
    status := .proven, prop := ``Contextlib.ClosingOnce, thm := some ``Contextlib.closingOnce_proven },
  { id := "misc-ctx-nullcontext", pyFile := "Lib/contextlib.py"
    pyFns := ["nullcontext.__init__", "nullcontext.__enter__", "nullcontext.__exit__",
              "nullcontext.__aenter__", "nullcontext.__aexit__"]
    statement := "with nullcontext(v) as x: body is body with x = v, value or exception."
    source := "docstring of nullcontext"
    status := .proven, prop := ``Contextlib.NullcontextTransparent, thm := some ``Contextlib.nullcontextTransparent_proven },
  { id := "misc-ctx-redirect", pyFile := "Lib/contextlib.py"
    pyFns := ["_RedirectStream.__init__", "_RedirectStream.__enter__", "_RedirectStream.__exit__"]
    statement := "__enter__ installs and returns the target and the matching __exit__ restores the stream and the object's state, re-entrantly; __exit__ alone is IndexError."
    source := "comment Lib/contextlib.py:461"
    status := .proven, prop := ``Contextlib.RedirectRestores, thm := some ``Contextlib.redirectRestores_proven },
  { id := "misc-ctx-chdir", pyFile := "Lib/contextlib.py"
    pyFns := ["chdir.__init__", "chdir.__enter__", "chdir.__exit__"]
    statement := "The matching __exit__ returns to the directory __enter__ found; a failing os.chdir propagates, with the saved directory left on the stack."
    source := "docstring of chdir"
    status := .proven, prop := ``Contextlib.ChdirRestores, thm := some ``Contextlib.chdirRestores_proven },
  { id := "misc-ctx-suppress-plain", pyFile := "Lib/contextlib.py"
    pyFns := ["suppress.__init__", "suppress.__enter__", "suppress.__exit__"]
    statement := "suppress.__exit__ is None without an exception, True for a listed class, False otherwise."
    source := "docstring of suppress"
    status := .proven, prop := ``Contextlib.SuppressPlain, thm := some ``Contextlib.suppressPlain_proven },
  { id := "misc-ctx-suppress-group", pyFile := "Lib/contextlib.py"
    pyFns := ["suppress.__exit__"]
    statement := "On a flat exception group: all members matching suppresses it; otherwise a new group with the unsuppressed members in order, and the original's message, cause and traceback, is raised, also when no member matches."
    source := "Doc/library/contextlib.rst:316-319"
    status := .proven, prop := ``Contextlib.SuppressGroup, thm := some ``Contextlib.suppressGroup_proven
    notes := "Nested groups are difftested, not covered by the theorem." },
  { id := "misc-ctx-exit-matches-nested", pyFile := "Lib/contextlib.py"
    pyFns := ["ExitStack.__exit__"]
    statement := "For every stack and behaviour of the callbacks, the exception leaving a with ExitStack() block is the one leaving the equivalent nested with statements."
    source := "comment Lib/contextlib.py:634-635, :592-593"
    status := .proven, prop := ``Contextlib.ExitMatchesNested, thm := some ``Contextlib.exitMatchesNested_proven
    notes := "__context__ is outside the statement: it differs in the open python/cpython#102201." },
  { id := "misc-ctx-exit-lifo", pyFile := "Lib/contextlib.py"
    pyFns := ["ExitStack.__exit__"]
    statement := "Callbacks run from the last pushed to the first, each once, and the stack ends empty, when the walk of _fix_exception_context ends."
    source := "comment Lib/contextlib.py:651"
    status := .proven, prop := ``Contextlib.ExitLifo, thm := some ``Contextlib.exitLifo_proven },
  { id := "misc-ctx-exit-terminates", pyFile := "Lib/contextlib.py"
    pyFns := ["ExitStack.__exit__", "AsyncExitStack.__aexit__"]
    statement := "ExitStack.__exit__ terminates for every exception a callback raises."
    source := "invariant: no hang; Python/errors.c:203-205 guards the same walk against pre-existing cycles"
    status := .refuted, prop := ``Contextlib.ExitStackTerminates,
    thm := some ``Contextlib.exitStackTerminates_refuted
    bug := some "corelibs-exitstack-context-cycle-hang"
    notes := "A cycle in __context__ that contains neither None, old_exc nor frame_exc keeps the while 1 of _fix_exception_context running." },
  { id := "misc-ctx-exit-keeps-context-acyclic", pyFile := "Lib/contextlib.py"
    pyFns := ["ExitStack.__exit__", "AsyncExitStack.__aexit__"]
    statement := "ExitStack.__exit__ does not create a cycle in __context__ when the callbacks do not."
    source := "comment Lib/contextlib.py:634-635; Python/errors.c:203-208 keeps nested with statements acyclic"
    status := .refuted, prop := ``Contextlib.ExitKeepsContextAcyclic,
    thm := some ``Contextlib.exitKeepsContextAcyclic_refuted
    bug := some "corelibs-exitstack-context-cycle-hang"
    notes := "A callback re-raising an exception that is in the chain of the current one: new_exc.__context__ = old_exc closes a cycle." },
  { id := "misc-ctx-stack-registration", pyFile := "Lib/contextlib.py"
    pyFns := ["_BaseExitStack.__init__", "_BaseExitStack.pop_all", "_BaseExitStack.push",
              "_BaseExitStack.enter_context", "_BaseExitStack.callback",
              "_BaseExitStack._push_exit_callback", "ExitStack.__enter__", "AsyncExitStack.__aenter__",
              "AsyncExitStack.enter_async_context", "AsyncExitStack.push_async_exit",
              "AsyncExitStack.push_async_callback"]
    statement := "push registers what _lookup_special gives or the callable and registers nothing if __get__ raises, callback a wrapper, enter_context looks up __enter__ then __exit__ before running anything and pushes only after __enter__ succeeded, pop_all moves everything; async entries carry is_sync False."
    source := "docstrings of _BaseExitStack"
    status := .proven, prop := ``Contextlib.StackRegistration, thm := some ``Contextlib.stackRegistration_proven },
  { id := "misc-ctx-lookup-special", pyFile := "Lib/contextlib.py"
    pyFns := ["_lookup_special"]
    statement := "_lookup_special gives the default when the type has no such attribute, the object itself for a class or an object with no __get__, and otherwise what __get__ gave, including its exception."
    source := "Lib/contextlib.py:534-542; Lib/inspect.py:2420-2426"
    status := .proven, prop := ``Contextlib.LookupSpecialFollowsDescriptor,
    thm := some ``Contextlib.lookupSpecialFollowsDescriptor_proven },
  { id := "misc-ctx-callback-cannot-suppress", pyFile := "Lib/contextlib.py"
    pyFns := ["_BaseExitStack._create_cb_wrapper", "AsyncExitStack._create_async_cb_wrapper"]
    statement := "The wrapper of callback ignores the exception details and returns false, so it cannot suppress."
    source := "docstring of callback"
    status := .proven, prop := ``Contextlib.CallbackCannotSuppress, thm := some ``Contextlib.callbackCannotSuppress_proven },
  { id := "misc-ctx-async-exit-matches", pyFile := "Lib/contextlib.py"
    pyFns := ["AsyncExitStack.__aexit__", "AsyncExitStack.aclose", "ExitStack.close"]
    statement := "Over sync entries __aexit__ is __exit__ plus the StopIteration conversion of an async def; close and aclose are the exit with no exception."
    source := "invariant: sync and async siblings"
    status := .proven, prop := ``Contextlib.AsyncExitMatches, thm := some ``Contextlib.asyncExitMatches_proven }
]

def weakrefEntries : List Entry := [
  { id := "misc-wvd-reads", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.__getitem__", "WeakValueDictionary.__len__",
              "WeakValueDictionary.__contains__", "WeakValueDictionary.__repr__",
              "WeakValueDictionary.get", "WeakValueDictionary.items", "WeakValueDictionary.keys",
              "WeakValueDictionary.itervaluerefs", "WeakValueDictionary.values",
              "WeakValueDictionary.valuerefs"]
    statement := "For distinct keys, __getitem__, get and in agree with items(), and keys() and values() are its columns."
    source := "docstring of WeakValueDictionary"
    status := .proven, prop := ``Weakref.WVD.WvdReads, thm := some ``Weakref.WVD.wvdReads_proven },
  { id := "misc-wvd-death", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.__init__", "KeyedRef.__new__", "KeyedRef.__init__"]
    statement := "When an object dies the live items lose exactly it, and with the callback its entries leave data."
    source := "docstring of WeakValueDictionary"
    status := .proven, prop := ``Weakref.WVD.WvdDeath, thm := some ``Weakref.WVD.wvdDeath_proven },
  { id := "misc-wvd-writes", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.__setitem__", "WeakValueDictionary.__delitem__"]
    statement := "d[k] = v makes d[k] give a live v and leaves other keys; an int raises TypeError; del removes the key or raises KeyError."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WVD.WvdWrites, thm := some ``Weakref.WVD.wvdWrites_proven },
  { id := "misc-wvd-pop-setdefault", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.pop", "WeakValueDictionary.setdefault"]
    statement := "pop returns a live value and removes it, and treats a dead one as missing; setdefault returns a live value and replaces a dead one."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WVD.WvdPopSetdefault, thm := some ``Weakref.WVD.wvdPopSetdefault_proven },
  { id := "misc-wvd-popitem", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.popitem"]
    statement := "popitem returns the last live item, dropping dead entries behind it, and raises KeyError when none is left."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WVD.WvdPopitem, thm := some ``Weakref.WVD.wvdPopitem_proven },
  { id := "misc-wvd-update", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.update"]
    statement := "update is __setitem__ of each item in turn, keywords after other."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WVD.WvdUpdate, thm := some ``Weakref.WVD.wvdUpdate_proven },
  { id := "misc-wvd-copy", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.copy", "WeakValueDictionary.__deepcopy__"]
    statement := "copy gives a new dictionary with the same live items; __deepcopy__ copies keys and shares values."
    source := "Doc/library/weakref.rst"
    status := .proven, prop := ``Weakref.WVD.WvdCopy, thm := some ``Weakref.WVD.wvdCopy_proven },
  { id := "misc-wvd-or", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.__or__", "WeakValueDictionary.__ror__", "WeakValueDictionary.__ior__"]
    statement := "In d | other other's value wins, in other | d a live value of d wins, a non-Mapping gives NotImplemented, and |= is update."
    source := "PEP 584"
    status := .proven, prop := ``Weakref.WVD.WvdOr, thm := some ``Weakref.WVD.wvdOr_proven },
  { id := "misc-wvd-init", pyFile := "Lib/weakref.py"
    pyFns := ["WeakValueDictionary.__init__", "KeyedRef.__new__", "KeyedRef.__init__"]
    statement := "__init__ updates an empty dictionary; a KeyedRef holds the referent and the key, refuses what cannot be referenced, and reads None once the referent is dead."
    source := "docstring of KeyedRef"
    status := .proven, prop := ``Weakref.WVD.WvdInit, thm := some ``Weakref.WVD.wvdInit_proven },
  { id := "misc-wkd-non-weak", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__contains__", "WeakKeyDictionary.__getitem__",
              "WeakKeyDictionary.get", "WeakKeyDictionary.__setitem__", "WeakKeyDictionary.__delitem__",
              "WeakKeyDictionary.pop", "WeakKeyDictionary.setdefault"]
    statement := "With a key that cannot be weakly referenced, in says False and the other operations raise the TypeError of ref()."
    source := "Lib/weakref.py:359-364"
    status := .proven, prop := ``Weakref.WKD.WkdNonWeak, thm := some ``Weakref.WKD.wkdNonWeak_proven },
  { id := "misc-wkd-reads", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__getitem__", "WeakKeyDictionary.get", "WeakKeyDictionary.__contains__",
              "WeakKeyDictionary.__len__", "WeakKeyDictionary.__repr__", "WeakKeyDictionary.items",
              "WeakKeyDictionary.keys", "WeakKeyDictionary.values", "WeakKeyDictionary.keyrefs"]
    statement := "d[k], get and in report the entry whose ref equals ref(k); keys() and values() are the columns of items()."
    source := "docstring of WeakKeyDictionary"
    status := .proven, prop := ``Weakref.WKD.WkdReads, thm := some ``Weakref.WKD.wkdReads_proven },
  { id := "misc-wkd-writes", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__setitem__"]
    statement := "With == an equivalence, d[k] = v makes d[k] give v for a live k and leaves every key not equal to k."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WKD.WkdWrites, thm := some ``Weakref.WKD.wkdWrites_proven },
  { id := "misc-wkd-pop-setdefault", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__delitem__", "WeakKeyDictionary.pop", "WeakKeyDictionary.setdefault"]
    statement := "del, pop and setdefault follow the entry for k."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WKD.WkdPopSetdefault, thm := some ``Weakref.WKD.wkdPopSetdefault_proven },
  { id := "misc-wkd-death", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__init__"]
    statement := "When a key dies the live items lose it, and with the callback its entry leaves data."
    source := "docstring of WeakKeyDictionary"
    status := .proven, prop := ``Weakref.WKD.WkdDeath, thm := some ``Weakref.WKD.wkdDeath_proven },
  { id := "misc-wkd-popitem", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.popitem"]
    statement := "popitem returns the last entry with a live key and raises KeyError when none is left."
    source := "collections.abc.MutableMapping"
    status := .proven, prop := ``Weakref.WKD.WkdPopitem, thm := some ``Weakref.WKD.wkdPopitem_proven },
  { id := "misc-wkd-copy", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.copy", "WeakKeyDictionary.__deepcopy__"]
    statement := "While the live keys are pairwise different, a copy maps every live key to the same value and the deep copy to a copy of it."
    source := "Doc/library/weakref.rst"
    status := .proven, prop := ``Weakref.WKD.WkdCopy, thm := some ``Weakref.WKD.wkdCopy_proven },
  { id := "misc-wkd-or", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__or__", "WeakKeyDictionary.__ror__", "WeakKeyDictionary.__ior__",
              "WeakKeyDictionary.update"]
    statement := "In d | other other's value wins, in other | d a live key of d wins, a non-Mapping gives NotImplemented, and keywords to update raise TypeError."
    source := "PEP 584"
    status := .proven, prop := ``Weakref.WKD.WkdOr, thm := some ``Weakref.WKD.wkdOr_proven },
  { id := "misc-wkd-init", pyFile := "Lib/weakref.py"
    pyFns := ["WeakKeyDictionary.__init__", "WeakKeyDictionary.update"]
    statement := "__init__ updates an empty dictionary, and a list of pairs goes through dict() first."
    source := "Lib/weakref.py:309-320"
    status := .proven, prop := ``Weakref.WKD.WkdInit, thm := some ``Weakref.WKD.wkdInit_proven },
  { id := "misc-weakmethod-basics", pyFile := "Lib/weakref.py"
    pyFns := ["WeakMethod.__new__", "WeakMethod.__call__", "WeakMethod.__eq__", "WeakMethod.__ne__"]
    statement := "__new__ refuses what is no bound method, __call__ rebuilds the method while both referents live, __ne__ negates __eq__, and a dead weak method equals only itself."
    source := "Doc/library/weakref.rst"
    status := .proven, prop := ``Weakref.WeakMethodBasics, thm := some ``Weakref.weakMethodBasics_proven },
  { id := "misc-weakmethod-callback-once", pyFile := "Lib/weakref.py"
    pyFns := ["WeakMethod.__new__"]
    statement := "The callback of a WeakMethod runs at most once, at the first death of the object or the function."
    source := "Lib/weakref.py:53-60"
    status := .proven, prop := ``Weakref.WeakMethodCallbackOnce, thm := some ``Weakref.weakMethodCallbackOnce_proven },
  { id := "misc-finalize-once", pyFile := "Lib/weakref.py"
    pyFns := ["finalize.__call__", "finalize.detach", "finalize.peek", "finalize.alive", "finalize.atexit"]
    statement := "The first call runs the function and later ones return None; detach kills and peek keeps; shutdown stops the call; atexit reads and writes the flag."
    source := "docstring of finalize"
    status := .proven, prop := ``Weakref.Fin.FinalizeOnce, thm := some ``Weakref.Fin.finalizeOnce_proven },
  { id := "misc-finalize-init", pyFile := "Lib/weakref.py"
    pyFns := ["finalize.__init__", "finalize.__repr__"]
    statement := "__init__ registers a live finalizer and marks the registry dirty, a non-referenceable target registers nothing, and __repr__ says dead or names the object."
    source := "docstring of finalize"
    status := .proven, prop := ``Weakref.Fin.FinalizeInit, thm := some ``Weakref.Fin.finalizeInit_proven },
  { id := "misc-finalize-select", pyFile := "Lib/weakref.py"
    pyFns := ["finalize._select_for_exit"]
    statement := "_select_for_exit is a permutation of the finalizers with atexit true, by ascending index."
    source := "comment Lib/weakref.py:538"
    status := .proven, prop := ``Weakref.Fin.SelectForExit, thm := some ``Weakref.Fin.selectForExit_proven },
  { id := "misc-finalize-exitfunc", pyFile := "Lib/weakref.py"
    pyFns := ["finalize._exitfunc"]
    statement := "With functions that neither fail nor create finalizers, _exitfunc runs each selected finalizer once, newest first, and sets _shutdown."
    source := "docstring of finalize"
    status := .proven, prop := ``Weakref.Fin.ExitfuncOrder, thm := some ``Weakref.Fin.exitfuncOrder_proven }
]

def entries : List Entry :=
  graphlibEntries ++ schedEntries ++ queueEntries ++ numbersEntries ++ keywordEntries ++
    typesEntries ++ contextlibEntries ++ weakrefEntries

end PyLean.CoreLibs.Misc
