Section stream.
  Variable A : Type.
  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
Set Implicit Arguments.
End stream.

CoFixpoint zeroes : stream nat := Cons nat 0 zeroes.
(*CoFixpoint trues_falses : stream bool := Cons True*)