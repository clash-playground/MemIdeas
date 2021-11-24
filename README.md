# MemIdeas
Ideas for a consistent, (almost) universal model of memory in Clash


## Motivation
Clash gives a very natural representation of combinatorial logic.
It's super easy to write nice clean circuits that don't involve any memory.
Even simple memory operations can be modelled nicely with the built-in register primitives.
But the simplicity and consistency start to break down when memory interactions get more complex.

The language lends itself to Mealy machines.
If I wanted to write a really simple dataloop circuit whose state is just stored in a register,
I'd do something like:
```haskell
data MyCircuitIn = ...
data MyCircuitOut = ...
data MyCircuitState = ...

myCircuit :: MyCircuitIn -> MyCircuitState -> (MyCircuitOut, MyCircuitState)
myCircuit input oldState = ...

topEntity = mealy myCircuit myCircuitInitState
```

Imagine, though, that my circuit's state is more complex.
Suppose that I want to model a memory object that might have some control to it: a queue, for example.
Further suppose that our queue can on any given clock cycle do nothing, have a value pushed to it,
or have a value popped off of it.
If I want to keep the nice Mealy structure, it's not really clear what to do.
The queue is going to take as input not only a value, but also some control signals.
But it will only output a value.

I have a lot of circuits like this example with the queue in my work.
My immediate naive solution was:
```haskell
data MyCircuitIn = ...
data MyCircuitOut = ...

data MyCircuitState1 = MyCircuitState1
  { state1QueuePop :: Bool
  , state1QueuePush :: Bool
  , state1QueueValue :: QueueValue }
  
data MyCircuitState2 = MyCircuitState2
  { state2QueueValue :: QueueValue }
  
saveMyCircuitState :: HiddenClockResetEnable dom => Signal dom MyCircuitState1 -> MyCircuitState2
saveMyCircuitState oldState = newState where
  newState = MyCircuitState2 <$> queueValue'
  
  queueValue' = blockRam (repeat d32 (0 :: QueueValue)) queueRdAddr queueWrContent
  
  queueRdAddr = regEn 0 queuePop (queueRdAddr + 1)
  queuePop = state1QueuePop <$> oldState
  
  queueWrContent = (<*> queueWrAddr <*> queueValue <*> queuePush) $ pure $ \a v -> \case
    True -> Just (a, v)
    False -> Nothing
  queueWrAddr = regEn 0 queuePush (queueWrAddr + 1)
  queuePush = state1QueuePush <$> oldState
  queueValue = state1QueueValue <$> oldState

myCircuit :: MyCircuitIn -> MyCircuitState2 -> (MyCircuitOut, MyCircuitState1)
myCircuit input oldState = ...

mealyMyCircuit :: HiddenClockResetEnable dom => Signal dom MyCircuitIn -> Signal dom MyCircuitOut
mealyMyCircuit input = output where
  circOut = myCircuit <$> in <*> state
  state = saveMyCircuitState state'

  output = fst <$> circOut
  state' = snd <$> circOut
```
which... yikes.

In short: for each circuit, I ended up writing not only the circuit, but also implementations
of both a memory interface and a Mealy machine.
This seems like no good to me.
I think that if we know how some memory objects behave, we should be able to derive Mealy machines
for records built out of those objects.


## Solution
The solution I've come up with to the problem of complex memory has three steps.
First, we need to know how our memory objects get values when the circuit starts running (or resets).
Second, we should model commands to memory and know how memory will behave given those commands.
Finally, to avoid making two types for each derived record, we need a way to squeeze controls and
returns into a single datatype.

### Resetting
Consider RAM blocks.
Normally, we interact with them one value at a time: we save a value to a particular address,
and then we read a value from some other address.
But to _reset_ a RAM, we need to specify _every_ value in it simultaneously.

At first, I thought about a fairly natural approach, assuming I'd just figure out how to reset
"on the fly" given a controlling functor and a datatype:
```haskell
class MemoryWithFunctorControl (f :: * -> *) a where
  type ResetTy f a :: *
  
  saveMemory
    :: HiddenClockResetEnable dom
    => ResetTy f a
    -> Signal dom (f a)
    -> Signal dom a

instance KnownNat n => MemoryWithFunctorControl (RamControl n) a where
  type ResetTy (RamControl n) a = Vec n a
  
  saveMemory reset ramCmd =
    let rdAddr = ramReadAddress <$> ramCmd
        wrCont = ramWriteContent <$> ramCmd
    in blockRam reset rdAddr wrCont
```
However, Clash supports more than just `blockRam`.
There's also `blockRamU` whose reset type is `Index n -> a`.
Trying to implement both RAMs, it becomes apparent that we always end up with either annoyingly
many typeclass parameters, or annoyingly many data families.
Fortunately, this isn't the final solution.

The key realization is that a reset is specifying the "true value" of a memory object.
Each memory has an underlying type representing its contents, and while some of them have equvalent
interactions, they aren't necessarily storing values of the same type.
In fact, these underlying types determine uniquely _every other property_ of a memory.

So, a memory with a known reset is modelled by an underlying type.
Each underlying memory type has an _element_ type, which represents the values we can get at runtime
by interacting with that memory.
Therefore, our reset typeclass is simply:
```haskell
class KnownReset m where
  type MemElement m :: *
```
and the instances for the different RAM types are:
```haskell
newtype BlockRamUnderlying (n :: Nat) a =
  BlockRamUnderlying { unBlockRam :: Vec n a }

instance KnownReset (BlockRamUnderlying n a) where
  type MemElement (BlockRamUnderlying n a) = a

newtype BlockRamUUnderlying (n :: Nat) a =
  BlockRamUUnderlying { unBlockRamU :: Index n -> a }
  
instance KnownReset (BlockRamUUnderlying n a) where
  type MemElement (BlockRamUUnderlying n a) = a
```
(notice that both RAM types have the same element type, because we interact with them the same way).

### Saving
With the complicated essentialist business of resetting out of the way, we can move on to controlling
our base memory objects.
As briefly mentioned above, we want to control our memory's behaviour with functors.
A control functor lets us specify any of many possible actions that a memory object can do with some
data.

Consider again the queue.
Where before the queue had to be controlled with a bunch of Booleans, we can instead write a functor
```haskell
data QueueControl a
  = PopQueue
  | PushQueue a
  | DoNothing
```
which straightforwardly captures all the exclusive behaviours we want from the memory.
From there, we can write a save function for this type:
```haskell
data QueueUnderlying (n :: Nat) a = QueueUnderlying
  { headReset   :: Index n
  , tailReset   :: Index n
  , valueReset  :: Vec n a }

instance KnownReset (QueueUnderlying n a) where
  type MemElement (QueueUnderlying n a) = a

saveQueue
  :: ( KnownReset (QueueUnderlying n a)
     , HiddenClockResetEnable dom )
  => QueueUnderlying n a
  -> Signal dom (QueueControl a)
  -> Signal dom a
saveQueue (QueueUnderlying hdRst tlRst vRst) inControl = queueValue' where
  queueValue' = blockRam vRst tail wrCont
  
  tail = regEn tlRst doPop (tail + 1)
  head = regEn hdRst doPush (head + 1)
  
  doPop = inControl <&> \case
    PopQueue -> True
    _        -> False
  doPush = inControl <&> \case
    PushQueue _ -> True
  
  wrCont = (<*> head <*> inControl) $ pure $ \i -> \case
    PushQueue a -> Just (i, a)
    _           -> Nothing
```

We can generalize the save function for types with known controls to a class:
```haskell
class KnownReset m => KnownSave m where
  type MemControl m :: * -> *
  
  knownSave
    :: HiddenClockResetEnable dom
    => m
    -> Signal dom (MemControl m (MemElement m))
    -> Signal dom (MemElement m)
```


### Interacting
With the resetting and saving behaviour of a basic memory object defined, the last thing
we need is a way to use it.
Given what we have up to now, we're still in the unenviable situation of needing two types
for every memory operation: one with control functors applied, and one without.
Ideally, we'd like everything in a circuit's state to be captured by only one type.

In concurrent programming, there's a concept known as _transactional memory_.
The fundamental idea of transactional memory is that every memory interaction is atomic and comprises:
a read from memory, some work done on the value that was read, and a write back to memory.

The same sort of transactional shape is evident in a Mealy machine: we take the old state, run it through
a circuit, and get back a new state - all in one step.
We'll model a memory complete memory interaction with a simple wrapper type:
```haskell
data Mem r w = Mem
  { readMem :: r
  , toWrite :: w }
  
startMem :: r -> Mem r w
startMem r = Mem r undefined
```
A memory interaction starts with a value that's read, but no known write command yet.
The interaction is only complete when the circuit doing the interaction provides some data in `toWrite`.

Any memory type with an interaction defined on it will be an instance of the class
```haskell
class KnownReset m => AutoMem m where
  type MemInteract m :: *
  
  autoMem
    :: HiddenClockResetEnable dom
    => m
    -> Signal dom (MemInteract m)
    -> Signal dom (MemInteract m)
```
This class enables us to write Mealy machines for types with defined interactions as:
```haskell
autoMemMealy
  :: ( AutoMem m
     , HiddenClockResetEnable dom )
  => m
  -> ( i -> MemInteract m -> (o, MemInteract m) )
  -> Signal dom i
  -> Signal dom o
autoMemMealy reset circuit input = output where
  circOut = circuit <$> input <*> mem
  mem = autoMem reset mem'
  
  output = fst <$> circOut
  mem' = snd <$> circOut
  

data MyCircuitState = MyCircuitState
  { field1  :: Mem Field1Read Field1Write
  , field2  :: Mem Field2Read Field2Write }

instance AutoMem MyCircuitState where
  type MemInteract MyCircuitState = MyCircuitState

  autoMem _ myMem =
    MyCircuitState <$> autoMem undefined (field1 <$> myMem)
                   <*> autoMem undefined (field2 <$> myMem)

data MyCircuitIn
data MyCircuitOut

myCircuit :: MyCircuitIn -> MyCircuitState -> (MyCircuitOut, MyCircuitState)
myCircuit input state = ...

topEntity input = autoMemMealy undefined myCircuit input
```
As long as there's some type `FieldXUnderlying` such that `FieldXRead ~ MemElement FieldXUnderlying` and
`instance AutoMem FieldXUnderlying`, we can derive these composite instances automatically (with some
Template Haskell wizardry).
  
Obviously, instances of `KnownSave` have a defined memory interaction: they emit the current value, and
expect a new write command in return:
```haskell
type MemF f a = Mem a (f a)

instance (KnownReset m, KnownSave m) => AutoMem m where
  type MemInteract m = MemF (MemControl m) (MemElement m)
  
  autoSave reset =
    fmap startMem . knownSave reset . fmap toWrite
```

Here's where it gets good.
We can derive `AutoMem` instances for any type whose fields have `AutoMem` instances.
And we know that types with save behaviour have `AutoMem` instances.
So transitively, we can derive `AutoMem` instances for _any type whose fields have defined saving_.


## Conclusion
Taking everything together, we can look back at our first queue example and rewrite it as:
```haskell
data QueueUnderlying (n :: Nat) a = ...

instance KnownReset (QueueUnderlying n a) where ...
instance KnownSave (QueueUnderlying n a) where ...

type QueueMem a = MemF QueueControl a

data MyCircuitState = MyCircuitState
  { queueMem :: QueueMem QueueValue }

deriveAutoMem ''MyCircuitState


data MyCircuitIn
data MyCircuitOut

myCircuit :: MyCircuitIn -> MyCircuitState -> (MyCircuitOut, MyCircuitState)
myCircuit input oldState = newState where
  newState = MyCircuitState queue'
  
  queue' = writeMem $ computeQueueUpdate input queue
  queue = readMem $ queueMem oldState
  
  computeQueueUpdate input value = ...

topEntity input = autoMemMealy undefined myCircuit input
```
which looks a lot better than what we started with, I'd say.


## TODO
I still need to work out the best implementation for the `AutoMem` derivation.
Fortunately, with the framework established, that can be left as an implementation detail.

