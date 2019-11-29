Require Import Zee.lattice Zee.lang Zee.dec Zee.vals Zee.frame Zee.maplike Zee.sem.
Require Import Arith List Coq.Program.Basics Coq.Lists.ListSet Lia Coq.ZArith.BinInt.
Require Import Coq.Classes.RelationClasses.

Section TypeSystem.
  Context {A : Set} {BinOpS : Set} `{lattice A}.
  Definition Lab := @Lab A.
  Definition Ty := @Ty A.
  Definition LabVar := @LabVar A.
  Definition SecTy := @SecTy A.
  Definition SecTyV := @SecTyV A.
  Definition AtomSecTy := @AtomSecTy A.
  Definition Cmd := @Cmd A BinOpS.
  Definition Expr := @Expr A BinOpS.
  Definition V := @V A.

  Context {δ : string -> option Z}.
  Context {F: string -> option (list (string * Lab) *
                               list (string * Lab) *
                               list (string * SecTy) * Lab * Lab * Cmd) }.
  Context {eval_binop: BinOpS -> V -> V -> V}.
  Context {type_binop: BinOpS -> SecTy -> SecTy -> option SecTy}.
  Notation "'〚' o '〛' '(' e1 ',' e2 ')'" := (type_binop o e1 e2).

  Context {VarT ArgT LocT MemT : Type}
          {H_var_finmaplike: FinMapLike VarT string (A + SecTyV)}
          {H_arg_finmaplike: FinMapLike ArgT string SecTyV}
          {H_loc_finmaplike: FinMapLike LocT string SecTyV}
          {H_mem_maplike: MapLike MemT nat V}.
  Definition Frame := @Frame A VarT ArgT LocT MemT _ _ _ _.
  Definition PFrame := @PFrame A VarT ArgT LocT _ _ _.
  Definition EFrame := @EFrame A MemT _.
  
  Definition Formula := list (Lab * Lab).

  Global Instance Raiseable_AtomSecTy : Raiseable AtomSecTy (@Word A string) := {}.
  intros t k.
  destruct t.
  - exact (STy t (l ⊔ k)).
  - exact (VarTy s (l ⊔ k)).
  Defined.
  
  Global Instance Raiseable_SecTy : Raiseable SecTy (@Word A string) := {}.
  exact (fun s k => let fix visit s :=
                     match s with
                       ASecTy a => ASecTy (a ^^ k)
                     | ProdTy a s => ProdTy (a ^^ k) (visit s)
                     | NilTy => NilTy
                     end
                 in visit s).
  Defined.
  
  Definition TEnv := string -> option SecTy.
  
  Inductive Kind := KLabel | KType.
  Hint Constructors Kind.
  Definition KEnv := string -> option (Kind * Lab).

  Reserved Notation "pfr '⊨' ϕ" (at level 70, ϕ at next level).
  Inductive holds: PFrame -> Formula -> Prop :=
    holds_nil pfr: holds pfr nil
  | holds_cons pfr ϕ k1 k2:
      (forall ℓ₁ ℓ₂, ⟨k1, pfr⟩ₖ ⇓ₖ ℓ₁ -> ⟨k2, pfr⟩ₖ ⇓ₖ ℓ₂ -> ℓ₁ ⊑ ℓ₂) ->
      pfr ⊨ ϕ ->
      pfr ⊨ ((k1, k2) :: ϕ)
  where "pfr '⊨' ϕ" := (holds pfr ϕ).
  Hint Constructors holds.
  
  Definition flowsto_with (ϕ: Formula) (k1 k2 : Lab): Prop :=
    forall pfr ℓ₁ ℓ₂, pfr ⊨ ϕ ->
                 ⟨k1, pfr⟩ₖ ⇓ₖ ℓ₁ ->
                 ⟨k2, pfr⟩ₖ ⇓ₖ ℓ₂ -> ℓ₁ ⊑ ℓ₂.
  Notation "ϕ '⊢' k1 '⊑' k2" := (flowsto_with ϕ k1 k2) (at level 70, k1, k2 at next level).
  Notation "ϕ '⊢' k1 '===' k2" := (flowsto_with ϕ k1 k2 /\ flowsto_with ϕ k2 k1) (at level 70, k1, k2 at next level).
  
  Reserved Notation "ϕ '⊢' s1 '<:' s2 " (at level 70, s1, s2 at next level).
  Reserved Notation "ϕ '⊢ₐ' s1 '<:' s2 " (at level 70, s1, s2 at next level).
  
  Inductive subtype: Formula -> SecTy -> SecTy -> Prop :=
    sub_atom a1 a2 ϕ:
      ϕ ⊢ₐ a1 <: a2 ->
      ϕ ⊢ ASecTy a1 <: ASecTy a2
  | sub_prod ϕ (a1 a2 : AtomSecTy) s1 s2:
      ϕ ⊢ₐ a1 <: a2 ->
      ϕ ⊢ s1 <: s2 ->
      ϕ ⊢ a1 · s1 <: a2 · s2
   | sub_forget ϕ (a : AtomSecTy) s:
       ϕ ⊢ a · s <: a
   | sub_nil s ϕ: ϕ ⊢ s <: ε
   | sub_trans s2 ϕ s1 s3:
       ϕ ⊢ s1 <: s2 ->
       ϕ ⊢ s2 <: s3 ->
       ϕ ⊢ s1 <: s3
  where "ϕ '⊢' s1 '<:' s2 " := (subtype ϕ s1 s2) with
  subtype_atom: Formula -> AtomSecTy -> AtomSecTy -> Prop :=
    sub_atom_sty ϕ t k1 k2: ϕ ⊢ k1 ⊑ k2 -> ϕ ⊢ₐ STy t k1 <: STy t k2
  | sub_atom_var ϕ k1 k2 x: ϕ ⊢ k1 ⊑ k2 -> ϕ ⊢ₐ VarTy x k1 <: VarTy x k2
  where "ϕ '⊢ₐ' s1 '<:' s2 " := (subtype_atom ϕ s1 s2).
    
  Reserved Notation "'[' Π ',' ϕ ']' '⊢ₖ' k1 ':' k2" (at level 70, k1, k2 at next level).
  Inductive wt_lab: KEnv -> Formula -> Lab -> Lab -> Prop :=
    wt_labvar κ Π ϕ k: Π κ = Some (KLabel, k) ->
                       [Π, ϕ] ⊢ₖ WordVar κ : k
  | wt_lit Π ϕ (ℓ : A): [Π, ϕ] ⊢ₖ Lit ℓ : ⊥
  | wt_join Π ϕ k1 k2 k1' k2':
      [Π, ϕ] ⊢ₖ k1 : k1' ->
      [Π, ϕ] ⊢ₖ k2 : k2' ->
      [Π, ϕ] ⊢ₖ Join k1 k2 : k1' ⊔ k2'
  | wt_meet Π ϕ k1 k2 k1' k2':
      [Π, ϕ] ⊢ₖ k1 : k1' ->
      [Π, ϕ] ⊢ₖ k2 : k2' ->
      [Π, ϕ] ⊢ₖ Meet k1 k2 : k1' ⊔ k2'
  | wt_lab_sub ϕ Π k k1 k2:
      [Π, ϕ] ⊢ₖ k : k1 ->
      ϕ ⊢ k1 ⊑ k2 ->
      [Π, ϕ] ⊢ₖ k : k2              
  where "'[' Π ',' ϕ ']' '⊢ₖ' k1 ':' k2" := (wt_lab Π ϕ k1 k2).

  Global Instance is_dec_eq_string : is_dec_eq string := {}.
  exact string_dec.
  Defined.
  
  Reserved Notation "'[' Π ',' ϕ ']' '⊢ₛ' s ':' k" (at level 70, s, k at next level).
  Reserved Notation "'[' Π ',' ϕ ']' '⊢ₐ' a ':' k" (at level 70, a, k at next level).
  Reserved Notation "'[' Π ',' ϕ ']' '⊢ₜ' t ':' k" (at level 70, t, k at next level).
  
  Inductive wt_sectype: KEnv -> Formula -> SecTy -> Lab -> Prop :=
    wt_secty_atom a Π ϕ k: [Π, ϕ] ⊢ₐ a : k -> [Π, ϕ] ⊢ₛ ASecTy a : k
  | wt_secty_prod a s Π ϕ k1 k2:
      [Π, ϕ] ⊢ₐ a : k1 ->
      [Π, ϕ] ⊢ₛ s : k2 ->
      [Π, ϕ] ⊢ₛ a · s : k1 ⊔ k2
  | wt_secty_nil Π ϕ: [Π, ϕ] ⊢ₛ ε : ⊥
  | wt_secty_sub Π ϕ s k1 k2:
      [Π, ϕ] ⊢ₛ s : k1 ->
      ϕ ⊢ k1 ⊑ k2 ->
      [Π, ϕ] ⊢ₛ s : k2              
  where "'[' Π ',' ϕ ']' '⊢ₛ' s ':' k" := (wt_sectype Π ϕ s k) with
  wt_atom_sectype: KEnv -> Formula -> AtomSecTy -> Lab -> Prop :=
    wt_atom_ty t k Π ϕ k1 k2:
      [Π, ϕ] ⊢ₜ t : k1 ->
      [Π, ϕ] ⊢ₖ k : k2 ->
      [Π, ϕ] ⊢ₐ STy t k : k1 ⊔ k2
  | wt_atom_var α k1 k2 k Π ϕ:
      Π α = Some (KType, k1) ->
      [Π, ϕ] ⊢ₖ k : k2 ->
      [Π, ϕ] ⊢ₐ VarTy α k : k1 ⊔ k2
  | wt_atom_sub Π ϕ a k1 k2:
      [Π, ϕ] ⊢ₐ a : k1 ->
      ϕ ⊢ k1 ⊑ k2 ->
      [Π, ϕ] ⊢ₐ a : k2
  where "'[' Π ',' ϕ ']' '⊢ₐ' a ':' k" := (wt_atom_sectype Π ϕ a k) with
  wt_ty: KEnv -> Formula -> Ty -> Lab -> Prop :=
    wt_int Π ϕ: [Π, ϕ] ⊢ₜ IntTy : ⊥
  | wt_ptr Π ϕ s k k1 k2:
      [Π, ϕ] ⊢ₛ s : k1 ->
      [Π, ϕ] ⊢ₖ k : k2 ->
      [Π, ϕ] ⊢ₜ k # s : k1 ⊔ k2
  | wt_sptr Π ϕ s1 s2 k1 k2:
      [Π, ϕ] ⊢ₛ s1 : k1 ->
      [Π, ϕ] ⊢ₛ s2 : k2 ->
      [Π, ϕ] ⊢ₜ s1 @ s2 : k1 ⊔ k2
  | wt_exty Π ϕ k k' α s k'':
      [Π, ϕ] ⊢ₖ k : k' ->
      [Π[α ↦ (KType, k)], ϕ] ⊢ₛ s : k'' ->
      [Π, ϕ] ⊢ₜ (∃ₛ (α ::: k) s) : k' (* I hope we don't need to join with k'' *)
  | wt_exlab Π ϕ k k' κ s k'':
      [Π, ϕ] ⊢ₖ k : k' ->
      [Π[κ ↦ (KLabel, k)], ϕ] ⊢ₛ s : k'' ->
      [Π, ϕ] ⊢ₜ (∃ₖ (κ ::: k) s) : k' (* I hope we don't need to join with k'' *)
  | wt_rec Π ϕ α k k' s:
      [Π, ϕ] ⊢ₖ k : k' ->
      [Π[α ↦ (KType, k')], ϕ] ⊢ₛ s : k' ->
      [Π, ϕ] ⊢ₜ (μ (α ::: k) s) : k'
  | wt_size Π ϕ s k:
      [Π, ϕ] ⊢ₛ s : k ->
      [Π, ϕ] ⊢ₜ |s| : k
  | wt_ty_sub Π ϕ s k1 k2:
      [Π, ϕ] ⊢ₜ s : k1 ->
      ϕ ⊢ k1 ⊑ k2 ->
      [Π, ϕ] ⊢ₜ s : k2
  where "'[' Π ',' ϕ ']' '⊢ₜ' t ':' k" := (wt_ty Π ϕ t k).
  

  Definition T_st (pc fr k : Lab) : SecTy :=
    STy (μ ("α" ::: k)
           (STy (∃ₛ ("β" ::: fr)
                  (STy (∃ₛ ("γ" ::: fr)
                         (STy (VarTy "β" ⊥ · ASecTy (VarTy "α" ⊥) @ VarTy "γ" ⊥) pc)) ⊥)) ⊥)) ⊥.
  Notation "'Tₛₜ' '(' pc ',' fr ',' k ')'" := (T_st pc fr k).

  Class Substeable (A S B : Type) :=
    {
      subst : A -> S -> B -> B
    }.
  Notation "b '[[' a './' x ']]'" := (subst a x b) (at level 8, left associativity).

  Fixpoint subst_upto {A S B : Type} `{Substeable A S B} (i : nat) (as' : list A) (xs : list S) (b : B): B :=
    match i with
      0 => b
    | S i =>
      match as', xs with
        nil, _ => b
      | _, nil => b
      | a :: as', x :: xs => (subst_upto i as' xs b) [[ a ./ x ]]
      end
    end.
  Notation "b '[[' a './' x ']' i ']'" := (subst_upto i a x b) (at level 8, left associativity).

  Instance Substeable_many (A S B : Type) `{Substeable A S B}: Substeable (list A) (list S) B := {}.
  intros as' xs b.
  exact (b [[ as' ./ xs ] (length xs)]).
  Defined.
  
  Reserved Notation "Π1 '⊢ₚ' p '⇝' '[' k ']' Π2 ':' s" (at level 70, Π2, s at next level).
  Reserved Notation "Π1 '⊢ₐ' p '⇝' '[' k ']' Π2 ':' s" (at level 70, Π2, s at next level).
  Inductive make_kenv: KEnv -> SecPat -> Lab -> KEnv -> SecTy -> Prop :=
  | make_kenv_prod p1 p2 s1 s2 Π Π' Π'' k:
      Π ⊢ₐ p1 ⇝ [k] Π' : s1 ->
      Π' ⊢ₚ p2 ⇝ [k] Π'' : s2 ->
      Π ⊢ₚ p1 · p2 ⇝ [k] Π'' : s1 · s2
  | make_kenv_nil k Π:
      Π ⊢ₚ ε ⇝ [k] Π : ε
  | make_kenv_atom Π p k Π' s:
      Π ⊢ₐ p ⇝ [k] Π' : s ->
      Π ⊢ₚ p ⇝ [k] Π' : s
  where "Π₁ '⊢ₚ' p '⇝' '[' k ']' Π₂ ':' s" := (make_kenv Π₁ p k Π₂ s) with
  atom_make_kenv: KEnv -> AtomPat -> Lab -> KEnv -> AtomSecTy -> Prop :=
    atom_make_kenv_var α k Π:
      Π ⊢ₐ PVar α ⇝ [k] Π[α ↦ (KType, k)] : VarTy α ⊥
  | atom_make_kenv_int Π k κ:
      Π ⊢ₐ SPat PInt κ ⇝ [k] Π[κ ↦ (KLabel, k)] : STy IntTy (LabVar κ)
  | atom_make_kenv_sptr Π Π' Π'' k κ p1 p2 s1 s2:
      Π ⊢ₚ p1 ⇝ [k] Π' : s1 ->
      Π' ⊢ₚ p2 ⇝ [k] Π'' : s2 ->                 
      Π'' ⊢ₐ SPat (p1 @ p2) κ ⇝ [k] Π''[κ ↦ (KLabel, k)] : STy (s1 @ s2) (LabVar κ)
  | atom_make_kenv_ptr Π Π' k κ1 κ2 p s:
      Π ⊢ₚ p ⇝ [k] Π' : s ->                 
      Π ⊢ₐ SPat (κ1 # p) κ2 ⇝ [k]
        Π'[κ1 ↦ (KLabel, k)][κ2 ↦ (KLabel, k)] : STy (LabVar κ1 # s) (LabVar κ2)
  where "Π₁ '⊢ₐ' p '⇝' '[' k ']' Π₂ ':' s" := (atom_make_kenv Π₁ p k Π₂ s).

  Fixpoint prodSecTy (τ1 : SecTy) (τ2 : SecTy) : SecTy :=
    match τ1 with
      ASecTy a => ProdTy a τ2
    | ProdTy a τ => ProdTy a (prodSecTy τ τ2)
    | NilTy => τ2
    end.
  
  Fixpoint subst_secty_secty (s1 : SecTy) (x : string) (s2 : SecTy) :=
    let fix subst s : SecTy :=
        match s with
          ASecTy a =>
          match subst_secty_atom s1 x a with
            inl a => a
          | inr s => s
          end
        | ProdTy a s =>
          match subst_secty_atom s1 x a with
            inl a => ProdTy a (subst s)
          | inr s' => prodSecTy s' (subst s)
          end
        | NilTy => NilTy
        end
    in subst s2 with
  subst_secty_atom (s1 : SecTy) (x : string) (a : AtomSecTy) : AtomSecTy + SecTy :=
    let fix subst a : AtomSecTy + SecTy :=
        match a with
          STy t k => inl (STy (subst_secty_ty s1 x t) k)
        | VarTy y k =>
          match (string_dec x y) with
            left _ => inr s1
          | right _ => inl (VarTy y k)
          end
        end
    in subst a with
  subst_secty_ty (s : SecTy) (x : string) (t : Ty) : Ty :=
    let fix subst t : Ty :=
        match t with
        | IntTy => IntTy
        | PtrTy k s' => PtrTy k (subst_secty_secty s x s')
        | SPtrTy s1 s2 => SPtrTy (subst_secty_secty s x s1) (subst_secty_secty s x s2)
        | ExTyTy α k s' =>
          ExTyTy α k
                 (match string_dec x α with
                    left _ => s'
                  | right _ => subst_secty_secty s x s'
                  end)
        | ExLabTy κ k s' =>
          ExLabTy κ k
                  (match string_dec x κ with
                     left _ => s'
                   | right _ => subst_secty_secty s x s'
                   end)
        | RecTy k y s' => RecTy k y
          (match string_dec x y with
             left _ => s'
           | right _ => subst_secty_secty s x s'
           end)
        | SizeTy s' => SizeTy (subst_secty_secty s x s')
        end
    in subst t. 
  
  Instance Substeable_SecTy_SecTy : Substeable SecTy string SecTy := {}.
  exact subst_secty_secty.
  Defined.

  Instance Substeable_SecTy_Expr : Substeable SecTy string Expr := {}.
  exact (fun s x e =>
           let fix subst e :=
               match e with
               | Var x => Var x
               | Num n => Num n
               | BinOp o e1 e2 => BinOp o (subst e1) (subst e2)
               | Unroll e => Unroll (subst e)
               | Roll e => Roll (subst e)
               | PackTy s1 e k α s2 =>
                 PackTy s1[[s ./ x]] (subst e) k α
                        (match string_dec x α with
                           left _ => s2
                         | right _ => s2[[s ./ x]]
                         end)
               | PackLab k1 e k2 κ s' =>
                 PackLab k1 (subst e) k2 κ
                        (match string_dec x κ with
                           left _ => s'
                         | right _ => s'[[s ./ x]]
                         end)
               | SizeOf s' => SizeOf s'[[s ./ x]]
               | AddrOf x => AddrOf x
               end
           in subst e).
  Defined.

  Instance Substeable_list (A S B : Type) `{Substeable A S B} : Substeable A S (list B) := {}.
  exact (fun a x bs =>
           let fix subst bs :=
               match bs with
                 nil => nil
               | b :: bs' => b [[ a ./ x ]] :: subst bs'
               end
           in subst bs).
  Defined.

  Class Binds (A : Type) := binds : string -> A -> bool.
  
  Fixpoint binds_pat (x : string) (p : SecPat) : bool :=
    match p with
      PProd a p => binds_atompat x a || binds_pat x p 
    | PNil => false
    | PAtom a => binds_atompat x a
    end
  with binds_atompat (x : string) (a : AtomPat) : bool :=
         match a with
           SPat p κ => eqb x κ || binds_pat' x p
         | PVar α => eqb x α
         end
  with binds_pat' (x : string) (p : Pat) : bool :=
         match p with
           PInt => false
         | PSPtr p1 p2 => binds_pat x p1 || binds_pat x p2
         | PPtr κ p => eqb x κ || binds_pat x p
         end.
  
  Instance Binds_SecPat : Binds SecPat := {}.
  eapply binds_pat.
  Defined.

  Instance Binds_AtomPat : Binds AtomPat := {}.
  eapply binds_atompat.
  Defined.

  Instance Binds_Pat : Binds Pat := {}.
  eapply binds_pat'.
  Defined.

  Fixpoint subst_secty_cmd (s : SecTy) (x : string) (c : Cmd) : Cmd :=
    let fix subst c :=
        match c with
        | CSkip => CSkip
        | CLet y s' e c =>
          CLet y s'[[ s ./ x  ]] e[[ s ./ x ]]
               match string_dec x y with
                 left _ => c
               | right _ => subst c
               end
        | CIf e c1 c2 => CIf e[[ s ./ x ]] (subst c1) (subst c2)
        | CWhile e c => CWhile e[[ s ./ x ]] (subst c)
        | CSeq c1 c2 => CSeq (subst c1) (subst c2)
        | CWrite e1 e2 => CWrite e1[[s ./ x]] e2[[s ./ x]]
        | CRead y e => CRead y e[[s ./ x]]
        | CAt k e c => CAt k e[[s ./ x]] (subst c)
        | CLabIf k1 k2 c1 c2 => CLabIf k1 k2 (subst c1) (subst c2)
        | CMatch α ps =>
          CMatch α (map (fun pc : (SecPat * Cmd) => let (p, c) := pc in
                                if binds x p then (p, c)
                                else (p, subst c)) ps)
        | CFP y => CFP y
        | CCall f ks ss es =>
          CCall f ks
                (map (subst_secty_secty s x) ss)
                (map (fun e => e [[ s ./ x ]]) es)
        | CUnpTy α k y s' e c =>
          CUnpTy α k y
                 (match string_dec x α with
                    left _ => s'
                  | right _ => s'[[ s ./ x ]]
                  end) e[[ s ./ x ]]
                 (match string_dec x α, string_dec x y with
                    right _, right _ => subst c
                  | _, _ => c
                  end)
        | CUnpLab κ k y s' e c =>
          CUnpLab κ k y
                  (match string_dec x κ with
                     left _ => s'
                   | right _ => s'[[ s ./ x ]]
                   end) e[[ s ./ x ]]
                  (match string_dec x κ, string_dec x y with
                     right _, right _ => subst c
                   | _, _ => c
                   end)
        | CDelay n => CDelay n
        | CUnsc y => CUnsc y
        | CEpi => CEpi
        | CStop => CStop
        end
    in subst c.
  
  Instance Substeable_SecTy_Cmd : Substeable SecTy string Cmd := {}.
  exact subst_secty_cmd.
  Defined.

  Instance Substeable_env {A S B : Type} `{Substeable A S B}: Substeable A S (S -> option B) := {}.
  intros a x f y.
  destruct (f y).
  - exact (Some (b [[a ./ x]])).
  - exact None.
  Defined.

  Instance Substeable_pair1 {A S B C : Type} `{Substeable A S B}: Substeable A S (B * C) | 10 := {}.
  intros a x [b c].
  exact (b [[a ./ x]], c).
  Defined.

  Instance Substeable_pair2 {A S B C : Type} `{Substeable A S C}: Substeable A S (B * C) | 10 := {}.
  intros a x [b c].
  exact (b, c [[a ./ x]]).
  Defined.

  Instance Substeable_pair {A S B C : Type} `{Substeable A S B} `{Substeable A S C}: Substeable A S (B * C) | 0 := {}.
  intros a x [b c].
  exact (b [[a ./ x]], c [[a ./ x]]).
  Defined.

  Instance Substeable_Lab_Lab : Substeable Lab string Lab := {}.
  exact (fun k1 x k2 =>
             let fix subst (k : Lab) : Lab :=
                 match k with
                   WordVar y =>
                   match string_dec x y with
                     left _ => k1
                   | right _ => WordVar y
                   end
                 | Lit a => Lit a
                 | Join w1 w2 => Join (subst w1) (subst w2)
                 | Meet w1 w2 => Meet (subst w1) (subst w2)
                 end
             in subst k2).
  Defined.

  Fixpoint subst_lab_secty (k : Lab) (x : string) (s2 : SecTy) :=
    let fix subst s : SecTy :=
        match s with
          ASecTy a => ASecTy (subst_lab_atom k x a)
        | ProdTy a s => ProdTy (subst_lab_atom k x a) (subst s)
        | NilTy => NilTy
        end
    in subst s2 with
  subst_lab_atom (k : Lab) (x : string) (a : AtomSecTy) : AtomSecTy :=
    let fix subst a : AtomSecTy :=
        match a with
          STy t k' => STy (subst_lab_ty k x t) k'[[k ./ x]]
        | VarTy y k' => VarTy y k'[[k ./ x]]
        end
    in subst a with
  subst_lab_ty (k : Lab) (x : string) (t : Ty) : Ty :=
    let fix subst t : Ty :=
        match t with
        | IntTy => IntTy
        | PtrTy k' s => PtrTy k[[k ./ x]] (subst_lab_secty k x s)
        | SPtrTy s1 s2 => SPtrTy (subst_lab_secty k x s1) (subst_lab_secty k x s2)
        | ExTyTy α k' s =>
          ExTyTy α k'[[k ./ x]] (match string_dec α x with
                                   left _ => s
                                 | right _ => subst_lab_secty k x s
                                 end)
        | ExLabTy κ k' s =>
          ExLabTy κ k'[[k ./ x]] (match string_dec κ x with
                                    left _ => s
                                  | right _ => subst_lab_secty k x s
                                  end)
        | RecTy k' y s => RecTy k'[[k ./ x]] y
                               (match string_dec x y with
                                  left _ => s
                                | right _ => subst_lab_secty k x s
                                end)
        | SizeTy s => SizeTy (subst_lab_secty k x s)
        end
    in subst t.
  
  Instance Substeable_Lab_SecTy : Substeable Lab string SecTy := {}.
  exact subst_lab_secty.
  Defined.
  
  Reserved Notation "'[' Γ ',' Π ',' ϕ ']' '⊢' e ':' r" (at level 70, e, r at next level).
  Inductive wt_expr: TEnv -> KEnv -> Formula -> Expr -> SecTy -> Prop :=
  | wt_var x Γ Π ϕ s:
      Γ x = Some s ->
      [Γ, Π, ϕ] ⊢ Var x : s
  | wt_num n Γ Π ϕ:
      [Γ, Π, ϕ] ⊢ Num n : STy IntTy ⊥
  | wt_binop Γ Π ϕ o e1 e2 s1 s2 s:
      [Γ, Π, ϕ] ⊢ e1 : s1 ->
      [Γ, Π, ϕ] ⊢ e2 : s2 ->
      〚o〛(s1, s2) = Some s ->
      [Γ, Π, ϕ] ⊢ BinOp o e1 e2 : s
  | wt_unroll Γ Π ϕ α k1 k2 s e:
      [Γ, Π, ϕ] ⊢ e : STy (μ (α ::: k1) s) k2 ->
      [Γ, Π, ϕ] ⊢ Unroll e : s [[ ASecTy (STy (μ (α ::: k1) s) k2) ./ α ]]
  | wt_roll Γ Π ϕ α k1 k2 s e:
      [Γ, Π, ϕ] ⊢ e : s [[ ASecTy (STy (μ (α ::: k1) s) k2) ./ α ]] ->
      [Γ, Π, ϕ] ⊢ Roll e : STy (μ (α ::: k1) s) k2
  | wt_packty Γ Π ϕ s e α k1 k2 s2:
      [Π, ϕ] ⊢ₛ s : k1 ->
      [Π[α ↦ (KType, k1)], ϕ] ⊢ₛ s2 : k2 ->
      [Γ, Π, ϕ] ⊢ e : s2[[ s ./ α ]] ->
      [Γ, Π, ϕ] ⊢ (TYPACK (s, e) AS ∃ ( α ::: k1 ) s2) : STy (∃ₛ (α ::: k1) s2) ⊥
  | wt_packlab Γ Π ϕ s1 e κ k1 k2 k s2:
      [Π, ϕ] ⊢ₖ k : k1 ->
      [Π[κ ↦ (KLabel, k1)], ϕ] ⊢ₛ s2 : k2 ->
      [Γ, Π, ϕ] ⊢ e : s2[[ s1 ./ κ ]] ->
      [Γ, Π, ϕ] ⊢ (LABPACK (k, e) AS ∃ ( κ ::: k1 ) s2) : STy (∃ₖ (κ ::: k1) s2) ⊥
  | wt_sizeof Γ Π ϕ s k:
      [Π, ϕ] ⊢ₛ s : k ->
      [Γ, Π, ϕ] ⊢ |s| : STy (|s|) k
  | wt_addrof Γ Π ϕ x s:
      Γ x = Some s -> 
      [Γ, Π, ϕ] ⊢ (&(x)) : STy (ε @ s) ⊥
  | wt_sub Γ Π ϕ e s1 s2:
      [Γ, Π, ϕ] ⊢ e : s1 ->
      ϕ ⊢ s1 <: s2 ->
      [Γ, Π, ϕ] ⊢ e : s2
  where "'[' Γ ',' Π ',' ϕ ']' '⊢' e ':' r" := (wt_expr Γ Π ϕ e r).

  Reserved Notation "'[' Γ ',' Π ',' ϕ ',' pc ',' fr ']' '⊢' c" (at level 70, c at next level).
  Inductive wt: TEnv -> KEnv -> Formula -> Lab -> Lab -> Cmd -> Prop :=
  | WtSkip Γ Π ϕ pc fr:
      [Γ, Π, ϕ, pc, fr] ⊢ SKIP
  | WtDelay Γ Π ϕ pc fr n:
      [Γ, Π, ϕ, pc, fr] ⊢ CDelay n
  | WtUnsc Γ Π ϕ pc fr x:
      [Γ, Π, ϕ, pc, fr] ⊢ CUnsc x
  | WtEpi Γ Π ϕ pc fr:
      [Γ, Π, ϕ, pc, fr] ⊢ CEpi
  | WtLet Γ Π ϕ pc fr x s r e c k:
      [Γ, Π, ϕ] ⊢ e : r ->
      [Π, ϕ] ⊢ₛ s : k ->
      ϕ ⊢ r ^^ pc <: s ->
      ϕ ⊢ k ⊑ fr ->                             
      [Γ[x ↦ s], Π, ϕ, pc, fr] ⊢ c ->
      [Γ, Π, ϕ, pc, fr] ⊢ LET x AS s ::= e IN c ENDLET
  | WtAt Γ Π ϕ pc fr k e c:
      [Π, ϕ] ⊢ₖ k : pc ->
      ϕ ⊢ k ⊑ pc ->
      [Γ, Π, ϕ] ⊢ e : STy IntTy pc ->
      [Γ, Π, ϕ, k, fr] ⊢ c ->
      [Γ, Π, ϕ, pc, fr] ⊢ AT k WITH BOUND e DO c TA
  | WtIf Γ Π ϕ pc fr e c1 c2:
      [Γ, Π, ϕ] ⊢ e : STy IntTy pc ->
      [Γ, Π, ϕ, pc, fr] ⊢ c1 ->
      [Γ, Π, ϕ, pc, fr] ⊢ c2 ->
      [Γ, Π, ϕ, pc, fr] ⊢ IF e THEN c1 ELSE c2 FI
  | WtFP Γ Π ϕ pc fr k1 x s:
      [Π, ϕ] ⊢ₖ fr : k1 ->
      Γ x = Some s ->
      ϕ ⊢ s ^^ pc <: Tₛₜ(pc, fr, k1) ->
      [Γ, Π, ϕ, pc, fr] ⊢ x <- FP
  | WtMatch Γ Π ϕ pc fr α ps k:
      Π α = Some (KType, k) ->
      ϕ ⊢ k ⊑ pc ->
      (forall i p c Π' s,
          nth_error ps i = Some (p, c) ->
          Π ⊢ₚ p ⇝ [k] Π' : s ->
          [ Γ[[ s ./ α]], Π, ϕ, pc, fr] ⊢ c[[ s ./ α ]]) ->
      [Γ, Π, ϕ, pc, fr] ⊢ CMatch α ps
  (* I don't think we need to consider k as we're TI (i.e., an out of bounds read/write will only leak the fact that we terminated).*)
  | WtRead Γ Π ϕ pc fr x e s s1 s2 k:
      [Γ, Π, ϕ] ⊢ e : STy (s1 @ s2) k ->
      Γ x = Some s ->
      ϕ ⊢ s2 ^^ pc <: s ->
      [Γ, Π, ϕ, pc, fr] ⊢ x =* e
  | WtWrite Γ Π ϕ pc fr e1 e2 s s1 s2 k:
      [Γ, Π, ϕ] ⊢ e1 : STy (s1 @ s2) k ->
      [Γ, Π, ϕ] ⊢ e2 : s ->
      ϕ ⊢ s ^^ pc <: s2 ->
      [Γ, Π, ϕ, pc, fr] ⊢ e1 *= e2
  | WtUnpTy Γ Π ϕ pc fr α k x s e c k1 k2 r:
      [Γ, Π, ϕ] ⊢ e : STy (∃ₛ (α ::: k1) r) pc ->
      ϕ ⊢ r ^^ pc <: s ->
      [Π[α ↦ (KType, k1)], ϕ] ⊢ₛ r : k2 ->
      [Γ[x ↦ s], Π[α ↦ (KType, k1)], ϕ, pc, fr ⊔ k1 ⊔ k2] ⊢ c ->
      [Γ, Π, ϕ, pc, fr] ⊢ UNPACKTY α AS TYPE k, x AS s ::= e IN c ENDUNPACKTY
  | WtUnpLab Γ Π ϕ pc fr κ k x s e c k1 k2 r:
      [Γ, Π, ϕ] ⊢ e : STy (∃ₖ (κ ::: k1) r) pc ->
      ϕ ⊢ r ^^ pc <: s ->
      [Π[κ ↦ (KLabel, k1)], ϕ] ⊢ₛ r : k2 ->
      [Γ[x ↦ s], Π[κ ↦ (KLabel, k1)], ϕ, pc, fr ⊔ k1 ⊔ k2] ⊢ c ->
      [Γ, Π, ϕ, pc, fr] ⊢ UNPACKLAB κ AS LABEL k, x AS s ::= e IN c ENDUNPACKLAB
  | WtIfLab Γ Π ϕ pc fr k1 k2 c1 c2:
      [Π, ϕ] ⊢ₖ k1 : pc ->
      [Π, ϕ] ⊢ₖ k2 : pc ->
      [Γ, Π, ϕ, pc, fr] ⊢ c1 ->
      [Γ, Π, ϕ, pc, fr] ⊢ c2 ->
      [Γ, Π, (k1, k2) :: ϕ, pc, fr] ⊢ IF k1 FLOWS k2 THEN c1 ELSE c2 FI
  | WtWhile Γ Π ϕ pc fr c e:
      [Γ, Π, ϕ] ⊢ e : STy IntTy pc ->
      [Γ, Π, ϕ, pc, fr] ⊢ c ->
      [Γ, Π, ϕ, pc, fr] ⊢ WHILE e DO c END
  | WtSeq Γ Π ϕ pc fr c1 c2:
      [Γ, Π, ϕ, pc, fr] ⊢ c1 ->
      [Γ, Π, ϕ, pc, fr] ⊢ c2 ->
      [Γ, Π, ϕ, pc, fr] ⊢ (c1 ;; c2)
  | WtCall Γ Π ϕ pc fr c f ks ss es f_ks1 f_ks2 f_ss f_fr f_pc:
      F f = Some (f_ks1, f_ks2, f_ss, f_fr, f_pc, c) ->
      length f_ks1 = length ks ->
      length f_ks2 = length ss ->
      length f_ss = length es ->
      (forall i kᵢ kᵢ' x, nth_error ks i = Some kᵢ ->
                    nth_error f_ks1 i = Some (x, kᵢ') ->
                    [Π, ϕ] ⊢ₖ kᵢ : kᵢ'[[ ks ./ (map fst f_ks1) ] i-1]) ->
      (forall i sᵢ kᵢ x, nth_error ss i = Some sᵢ ->
                   nth_error f_ks2 i = Some (x, kᵢ) ->
                   [Π, ϕ] ⊢ₛ sᵢ : kᵢ[[ ks ./ (map fst f_ks1) ]]) ->
      (forall i sᵢ eᵢ x, nth_error es i = Some eᵢ ->
                   nth_error f_ss i = Some (x, sᵢ) ->
                   [Γ, Π, ϕ] ⊢ eᵢ : sᵢ[[ ks ./ (map fst f_ks1) ]]
                                      [[ ss ./ (map fst f_ks2) ]]) ->
      ϕ ⊢ pc === f_pc[[ ks ./ (map fst f_ks1) ]] ->
      ϕ ⊢ fr ⊑ f_fr[[ ks ./ (map fst f_ks1) ]] ->
      [Γ, Π, ϕ, pc, fr] ⊢ CCall f ks ss es
  where "'[' Γ ',' Π ',' ϕ ',' pc ',' fr ']' '⊢' c" := (wt Γ Π ϕ pc fr c).
  
End TypeSystem.

Notation "'[' Γ ',' Π ',' ϕ ',' pc ',' fr ']' '⊢' c" := (wt Γ Π ϕ pc fr c) (at level 70, c at next level).