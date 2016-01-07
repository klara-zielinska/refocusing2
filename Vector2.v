Require Export Vector.


   Bind Scope vector_scope with Vector.t.
Delimit Scope vector_scope with vector.


Open Scope vector_scope.

Arguments nil {A}.
Arguments cons {A} _ {n} _.

Notation "[]"               := nil                                        : vector_scope.
Notation "[]( A )"          := (@nil A)                                   : vector_scope.
Notation "h :: t"           := (cons h t)              (at level 60, right associativity)
                                                                          : vector_scope.
Notation "[ x ]"            := (x :: [])                                  : vector_scope.
Notation "[ x ; .. ; y ]"   := (x :: .. (y :: []) ..)                     : vector_scope.
Notation "v [@ p ]"         := (nth v p)                  (at level 1, format "v [@ p ]")
                                                                          : vector_scope.
Infix "++" := append                                                      : vector_scope.


Definition Forall_split {A n} {v : Vector.t A n} {P} (H : Forall P v) : 
                                                         match v with 
                                                         | []      => True 
                                                         | x :: v' => P x /\ Forall P v' 
                                                         end :=

    match H                         in Forall _ v return match v with 
                                                         | []      => True 
                                                         | x :: v' => P x /\ Forall P v' 
                                                         end : Prop
    with 
    | Forall_nil              => I
    | Forall_cons n x v H0 H1 => conj H0 H1
    end.


Definition map2forall                {A B} (P : A -> Prop) (f : forall x : A, P x -> B) :
    forall {n} (v : Vector.t A n), Forall P v -> Vector.t B n :=

    fix aux {n} v H :=

        match v                               as v return match v with 
                                                   | []      => True 
                                                   | x :: v' => P x /\ Forall P v' 
                                                   end -> _ 
        with
        | []      => fun _ => []
        | x :: v' => fun H => let (H1, H2) := H in
                              f x H1 :: aux v' H2
        end

        (Forall_split H).

Close Scope vector_scope.
