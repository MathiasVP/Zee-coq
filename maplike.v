Require Import Zee.dec.
Require Import List Coq.Lists.ListSet.

Section MapLike.
  
  Reserved Notation "m '[' x '↦' v ']'" (at level 69, left associativity).
  Reserved Notation "m '?' a" (at level 60).
  
  Class ReadableMapLike (M : Type) (A B : Type) :=
    {
      lookup: M -> A -> option B
      where "m '?' a" := (lookup m a);
      empty_map : M;
      lookup_empty_map a: empty_map ? a = None
    }.
  Notation "m '?' a" := (lookup m a) (at level 60).
  Notation "∅" := empty_map.
  
  Class WriteableMapLike (M : Type) (A B : Type) :=
    {
      update: A -> B -> M -> M
      where "m '[' x '↦' v ']'" := (update x v m)
    }.
  Notation "m '[' x '↦' v ']'" := (update x v m) (at level 69, left associativity).
  
  Class MapLike (M : Type) (A B : Type) :=
    {
      is_readable :> ReadableMapLike M A B;
      is_writeable :> WriteableMapLike M A B;
      
      lookup_update_eq m x v: m[x ↦ v] ? x = Some v;
      lookup_update_neq m x y v: x <> y -> m[x ↦ v] ? y = m ? y
    }.

  Global Instance fun_readable_MapLike (A B : Type) `{is_dec_eq A} : ReadableMapLike (A -> option B) A B := {}.
  - intros f.
    assumption.
  - intros _.
    exact None.
  - intros.
    reflexivity.
  Defined.

  Global Instance fun_writeable_MapLike (A B : Type) `{is_dec_eq A} : WriteableMapLike (A -> option B) A B := {}.
  - exact (fun a b f a' =>
             match dec_eq a a' with
               left _ => Some b
             | right _ => f a'
             end).
  Defined.
  
  Global Instance fun_MapLike (A B : Type) `{is_dec_eq A} : MapLike (A -> option B) A B := {}.
  - intros.
    simpl.
    eapply dec_eq_refl.
  - intros.
    simpl.
    eapply dec_eq_neq.
    assumption.
  Defined.

  Global Instance list_readable_MapLike (A B : Type) `{is_dec_eq A} : ReadableMapLike (list (A * B)) A B := {}.
  - exact (fun xs x =>
             let fix visit xs :=
                 match xs with
                   nil => None
                 | (y, z) :: xs' =>
                   if dec_eq x y then
                     Some z
                   else visit xs'
                 end
             in visit xs).
  - exact nil.
  - intros.
    reflexivity.
  Defined.

  Global Instance list_writeable_MapLike (A B : Type) `{is_dec_eq A} : WriteableMapLike (list (A * B)) A B := {}.
  exact (fun x y xs =>
           let fix visit xs :=
               match xs with
                 nil => (x, y) :: nil
               | (x', y') :: xs' =>
                 if dec_eq x x' then
                   (x', y) :: xs'
                 else (x', y') :: visit xs'
               end
           in visit xs).
  Defined.
  
  Global Instance list_MapLike (A B : Type) `{is_dec_eq A} : MapLike (list (A * B)) A B := {}.
  - intros.
    induction m.
    + simpl.
      eapply dec_eq_refl.
    + simpl.
      destruct a as [a b].
      destruct (dec_eq x a).
      * subst.
        eapply dec_eq_refl.
      * rewrite -> dec_eq_neq by assumption.
        eapply IHm.
  - intros.
    simpl.
    induction m.
    + eapply dec_eq_neq.
      eauto.
    + destruct a as [a b].
      destruct (dec_eq x a).
      * subst.
        do 2 rewrite -> dec_eq_neq by eauto.
        reflexivity.
      * rewrite -> IHm.
        reflexivity.
  Defined.
  
  Class FinMapLike (M : Type) (A B : Type) :=
    {
      is_maplike :> MapLike M A B;
      values: M -> list (A * B);
      values_empty: values ∅ = nil;
      values_add m x v H:
        values (m [x ↦ v]) =
        (x, v) :: List.filter (fun p => if @dec_eq _ H (fst p) x then false else true) (values m)
    }.

  (*
  Fixpoint remove_dups {A B : Type} `{is_dec_eq A} (xs : list (A * B)) (s : set A) :=
    match xs with
      nil => nil
    | (a, b) :: xs' =>
      if set_mem dec_eq a s then
        remove_dups xs' s else
        (a, b) :: remove_dups xs' (set_add dec_eq a s)
    end.

  Lemma unfold_remove_dups_nil {A B : Type} `{is_dec_eq A}:
    forall s, @remove_dups A B _ nil s = nil.
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma unfold_remove_dups_cons {A B : Type} `{is_dec_eq A}:
    forall s a b xs, @remove_dups A B _ ((a, b) :: xs) s =
                if set_mem dec_eq a s then
                  remove_dups xs s else
                  (a, b) :: remove_dups xs (set_add dec_eq a s).
  Proof.
    intros.
    reflexivity.
  Qed.*)

  (*
  Global Instance list_FinMapLike (A B : Type) `{is_dec_eq A} : FinMapLike (list (A * B)) A B := {}.
  - exact id. 
  - reflexivity.
  - admit.
  Admitted.*)
  
End MapLike.

Notation "m '[' x '↦' v ']'" := (update x v m) (at level 69, left associativity).
Notation "m '?' a" := (lookup m a) (at level 60).
Notation "∅" := empty_map.