structure IndexedContainer (I O : Type 1) : Type 2 where
  command : O → Type 1
  response {o} : command o → Type
  next {o} (s : command o) : response s → I

namespace IndexedContainer

structure Extension {I O : Type 1} (C : IndexedContainer I O) (F : I → Type 1) (A : O) : Type 1 where
  shape : C.command A
  point (p : C.response shape) : F (C.next shape p)

scoped notation "⟦" C "⟧ " => Extension C
scoped notation command " ◃ " response " / " next => IndexedContainer.mk command response next

section ExampleVector


end ExampleVector


end IndexedContainer
