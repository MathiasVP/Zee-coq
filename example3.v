Require Import Autosubst.Autosubst.
Require Import Zee.lattice Zee.lang Zee.dec Zee.vals Zee.frame Zee.maplike Zee.sem Zee.typesystem.
Require Import Arith List Coq.Program.Basics Coq.Lists.ListSet Lia Coq.ZArith.BinInt.
Require Import Coq.Classes.RelationClasses.

Section Example3.
  Context {A : Set} {BinOpS : Set} `{lattice A}.
  Context {MINUS : BinOpS}.
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
  Context {type_binop: BinOpS -> SecTy -> SecTy -> SecTy -> Prop}.
  Context {VarT ArgT LocT MemT : Type}
          {H_var_finmaplike: FinMapLike VarT string (A + SecTyV)}
          {H_arg_finmaplike: FinMapLike ArgT string SecTyV}
          {H_loc_finmaplike: FinMapLike LocT string SecTyV}
          {H_mem_maplike: MapLike MemT nat V}.
  Definition Frame := @Frame A VarT ArgT LocT MemT _ _ _ _.
  Definition PFrame := @PFrame A VarT ArgT LocT _ _ _.
  Definition EFrame := @EFrame A MemT _.

  Notation "'〚' o '〛'" := (eval_binop o).
  Notation "o ':' s1 ',' s2 '⤇' s" := (type_binop o s1 s2 s) (at level 70, s at next level).
 
  Definition Var := @Var A BinOpS.
  Definition Num := @Num A BinOpS.
  Hint Unfold Var Num.
  Coercion Var: string >-> lang.Expr.
  Coercion Num: nat >-> lang.Expr.
  Coercion STy: lang.Ty >-> Funclass.
  (*Coercion eval_binop : BinOpS >-> Funclass.*)
  
  Definition public_varty (x : string) := VarTy x ⊥.
  Coercion public_varty: string >-> lang.AtomSecTy.

  Coercion SPat : lang.Pat >-> Funclass.
  Coercion PVar: string >-> AtomPat.

  Definition step_many := @step_many A BinOpS _ δ F eval_binop _ _ _ _ _ _ _ _.
  Notation "cfg1 '-->[' n ']' cfg2" := (step_many cfg1 cfg2 n) (at level 80).
  Notation "cfg1 '-->*' cfg2" := (exists n, cfg1 -->[n] cfg2) (at level 80).

  Definition wt := @wt A BinOpS _ F type_binop.
  Notation "'[' Γ ',' Π ',' ϕ ',' pc ',' fr ']' '⊢' c" := (wt Γ Π ϕ pc fr c) (at level 70, c at next level).
  Notation "'Tₛₜ' '(' pc ',' fr ',' k ')'" := (T_st pc fr k).
  
  Definition body_f : Cmd :=
    CALL "fun_g" nil nil nil.
 
  Definition body_g : Cmd :=
    LET "g_y" AS Tₛₜ(⊥, ⊥, ⊥) ::= 0 IN
    "g_y" <- FP;;
    UNPACKTY "β" AS TYPE ⊥,
             "g_z" AS (STy (∃ₛ ("γ" ::: ⊥)
                             (STy (VarTy "β" ⊥ · Tₛₜ(⊥, ⊥, ⊥) @ VarTy "γ" ⊥) ⊥)) ⊥) ::= Unroll "g_y" IN
    UNPACKTY "γ" AS TYPE ⊥,
             "g_w" AS (STy (VarTy "β" ⊥ · Tₛₜ(⊥, ⊥, ⊥) @ VarTy "γ" ⊥) ⊥) ::= "g_z" IN
    LET "g_y'" AS Tₛₜ(⊥, ⊥, ⊥) ::= 0
    IN "g_y'" =* BinOp MINUS "g_w" 1;;
    UNPACKTY "β'" AS TYPE ⊥,
             "g_z'" AS (STy (∃ₛ ("γ" ::: ⊥)
                              (STy (VarTy "β'" ⊥ · Tₛₜ(⊥, ⊥, ⊥) @ VarTy "γ" ⊥) ⊥)) ⊥) ::= "g_y'" IN
    UNPACKTY "γ'" AS TYPE ⊥,
             "g_w'" AS (STy (VarTy "β'" ⊥ · Tₛₜ(⊥, ⊥, ⊥) @ VarTy "γ'" ⊥) ⊥) ::= "g_z'" IN
    LET "g_y''" AS Tₛₜ(⊥, ⊥, ⊥) ::= 0
    IN "g_y''" =* BinOp MINUS "g_w'" 1;;
    UNPACKTY "β''" AS TYPE ⊥,
             "g_z''" AS (STy (∃ₛ ("γ" ::: ⊥)
                               (STy (VarTy "β''" ⊥ · Tₛₜ(⊥, ⊥, ⊥) @ VarTy "γ" ⊥) ⊥)) ⊥) ::= "g_y''" IN
    UNPACKTY "γ''" AS TYPE ⊥,
             "g_w''" AS (STy (VarTy "β''" ⊥ · Tₛₜ(⊥, ⊥, ⊥) @ VarTy "γ''" ⊥) ⊥) ::= "g_z''" IN
      MATCH "γ''" WITH
        (PInt "κ" · ε, "g_w''" *= 1)
      ENDMATCH
    ENDUNPACKTY
    ENDUNPACKTY
    ENDLET
    ENDUNPACKTY
    ENDUNPACKTY
    ENDLET
    ENDUNPACKTY
    ENDUNPACKTY
    ENDLET. 
    
  Definition program : Cmd :=
    LET "x" AS (IntTy ⊥) ::= 0
    IN CALL "fun_f" nil nil nil ENDLET.
  Hint Unfold program.
  
  Goal
    F "fun_f" = Some (nil, nil, nil, ⊥, ⊥, body_f) ->
    F "fun_g" = Some (nil, nil, nil, ⊥, ⊥, body_g) ->
    δ "x" = Some 0%Z ->
    δ "g_y" = Some 0%Z ->
    δ "g_z" = Some 1%Z ->
    δ "g_w" = Some 2%Z ->
    δ "g_y'" = Some 3%Z ->
    δ "g_z'" = Some 4%Z ->
    δ "g_w'" = Some 5%Z ->
    δ "g_y''" = Some 6%Z ->
    δ "g_z''" = Some 7%Z ->
    δ "g_w''" = Some 8%Z ->
    (forall n m, 〚 MINUS 〛 n m =
            match n, m with
              VNum n, VNum m => VNum (n - m)
            | VAddr a ν, VNum n => VAddr (a - n) ν
            | _, _ => VNum 0
            end) ->
    exists stk q,
      ⟨program, initial_stk program, 0, 0⟩ -->* ⟨CStop, stk, q, 2⟩ /\
      stk ? 0 + fp_of (initial_stk program) = Some (VNum 1).
  Proof.
  intros.
  do 2 eexists.
  split.
  {
    eexists.
    unfold program.
    eapply StepManyS.
    step_let.
    cbn. eapply StepManyS.
    step_seq.
    eapply SCall.
    + eassumption.
    + instantiate (1 := nil).
      reflexivity.
    + instantiate (1 := nil).
      reflexivity.
    + instantiate (1 := nil).
      reflexivity.
    + intros ? ? ? [? ?].
      eapply nth_error_In in H13. easy.
    + intros ? ? ? [? ?].
      eapply nth_error_In in H13. easy.
    + intros ? ? ? [? ?].
      eapply nth_error_In in H13. easy.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. constructor.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + reflexivity.
    + cbn. reflexivity.
    + easy.
    + eapply StepManyS.
      unfold body_f.
      step_seq.
      step_seq.
      eapply SCall.
      * eassumption.
      * instantiate (1 := nil).
        reflexivity.
      * instantiate (1 := nil).
        reflexivity.
      * instantiate (1 := nil).
        reflexivity.
      * intros ? ? ? [? ?].
        eapply nth_error_In in H13. easy.
      * intros ? ? ? [? ?].
        eapply nth_error_In in H13. easy.
      * intros ? ? ? [? ?].
        eapply nth_error_In in H13. easy.
      * cbn. reflexivity.
      * cbn. reflexivity.
      * cbn. constructor.
      * cbn. reflexivity.
      * cbn. reflexivity.
      * cbn. reflexivity.
      * cbn. reflexivity.
      * reflexivity.
      * cbn. reflexivity.
      * easy.
      * easy.
      * unfold body_g.
        cbn. eapply StepManyS.
        repeat step_seq; try easy.
        unfold T_st.
        step_let.
        easy.
        cbn. eapply StepManyS.
        repeat step_seq; try easy.
        eapply SFP.
        -- eassumption.
        -- cbn. reflexivity.
        -- cbn. reflexivity.
        -- cbn.
           repeat rewrite -> (values_add _ _ _ is_dec_eq_string).
           rewrite -> values_empty.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_unpack_ty.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           unfold T_st.
           step_unpack_ty.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_let.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           {
             eapply SRead.
             - eassumption.
             - cbn.
               rewrite <- (H12 (VAddr 4 2) (VNum 1)).
               eapply EBinOp; eval_expr.
             - cbn.
               simpl_mapsto.
               reflexivity.
           }
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_unpack_ty.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_unpack_ty.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_let.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           {
             eapply SRead.
             - eassumption.
             - cbn.
               erewrite <- (H12 (VAddr _ _) (VNum 1)).
               eapply EBinOp; eval_expr.
             - cbn.
               simpl_mapsto.
               rewrite -> lookup_empty_map.
               repeat rewrite -> (values_add _ _ _ _).
               repeat rewrite -> values_empty.
               cbn.
               reflexivity.
           }
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_unpack_ty.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           step_unpack_ty.
           easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           {
             eapply SMatch.
             - cbn.
               simpl_mapsto.
               reflexivity.
             - cbn.
               reflexivity.
             - repeat rewrite -> (values_add _ _ _ _).
               repeat rewrite -> values_empty.
               cbn.
               reflexivity.
           }               
           easy.
           repeat step_seq; try easy.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           {
             match goal with
               [ |- ⟨_, ?fr1 :: ?fr2 :: ?fr3 :: ?stk, _, _⟩ --> _] =>
               eapply (SWrite _ _ (fr1 :: fr2 :: nil) nil _ fr3)
             end.
             - reflexivity.
             - eapply EVar.
               + eassumption.
               + cbn.
                 simpl_mapsto.
                 reflexivity.
             - eval_expr.
             - cbn. lia.
             - cbn. lia.
           }
           eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn; eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           repeat step_seq; try easy.
           constructor.
           cbn. eapply StepManyS.
           constructor.
           eapply StepMany0.
  }
  {
    simpl_mapsto.
    reflexivity.
  }
  Qed.
  
End Example3.