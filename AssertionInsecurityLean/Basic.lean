import Mathlib

inductive TermVar
| cons : Nat -> TermVar

inductive KeyVar
| cons : Nat  -> KeyVar

inductive Name
| cons : Nat -> Name

def Var := Sum TermVar KeyVar


inductive Key: Type
| priv (k: Name)
| pub (k: Name)
| var (v: KeyVar)

inductive Term: Type
| var (v: TermVar)
| name (m: Name)
| key (k: Key)
| pair (t1 t2: Term)
| enc (t: Term) (k: Key)

abbrev TermSet := Set Term

def FVSetTerm : Term -> Set Var
| Term.var v => {Sum.inl v}
| Term.name _ => ∅ 
| Term.key (Key.var v) => {Sum.inr v}
| Term.key _ => ∅
| Term.pair t1 t2 =>  FVSetTerm t1 ∪ FVSetTerm t2
| Term.enc t' k => (FVSetTerm t') ∪
                           match k with 
                             | Key.var v => {Sum.inr v} 
                             | _ => ∅

inductive dy : TermSet -> Term -> Type
| ax {X: TermSet} {t: Term} (inH:  t ∈ X) : dy X t
| pk {X: TermSet} {k: Name} (kH: dy X (Term.key (Key.priv k)) ) : dy X (Term.key (Key.pub k))
                                                           
| splitL {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t1
| splitR {X: TermSet} {t1 t2: Term} (splitH: dy X (Term.pair t1 t2)) : dy X t2
| pair {X: TermSet} {t1 t2: Term} (tH: dy X t1) (uH: dy X t2) : dy X (Term.pair t1 t2)
                                                               
| sdec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.priv k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| senc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.priv k))) : dy X (Term.enc t (Key.priv k))
                                                                                     
| adec {X: TermSet} {t: Term} {k: Name} (encH: dy X (Term.enc t (Key.pub k))) (kH: dy X (Term.key (Key.priv k))): dy X t
| aenc {X: TermSet} {t: Term} {k: Name} (tH: dy X t) (kH: dy X (Term.key (Key.pub k))) : dy X (Term.enc t (Key.pub k))

noncomputable def TermMonotonicity (X Y: TermSet) : ∀   (t: Term), (dy X t) → (X ⊆ Y) →  (dy Y t) :=
  by
    intros t dyxt subset
    induction dyxt with
    | ax inH => exact dy.ax (subset inH)
    | pk _ kH_ih => exact dy.pk kH_ih  
    | splitL _ splitH_iH => exact dy.splitL splitH_iH
    | splitR _ splitH_iH => exact dy.splitR splitH_iH
    | pair _ _ tH_iH uH_iH => exact dy.pair tH_iH uH_iH
    | sdec _ _ encH_iH kH_iH => exact dy.sdec encH_iH kH_iH
    | senc _ _ tH_ih kH_iH => exact dy.senc tH_ih kH_iH
    | adec _ _ encH_iH kH_iH => exact dy.adec encH_iH kH_iH
    | aenc _ _ tH_ih kH_iH =>  exact dy.aenc tH_ih kH_iH

-- def isNormal {X: TermSet} {t: Term} (proof: dy X t): Bool :=
--   by
--     cases proof with

-- inductive normalProof: ∀ {X: TermSet} {t: Term}, dy X t → Prop
-- | ax {X: TermSet} {t: Term} (inH:  t ∈ X) : normalProof (dy.ax inH)
-- | pk {X: TermSet} {k: Name} {kH: dy X (Term.key (Key.priv k))} (kN: normalProof kH) 
--      : normalProof (dy.pk kH)
-- | pair {X: TermSet} {t1 t2: Term} {tH: dy X t1} {uH: dy X t2} 
--      (tN: normalProof tH) (uN: normalProof uH)
--      : normalProof (dy.pair tH uH)
-- | senc {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.priv k))} (tN: normalProof tH) (kN: normalProof kH): normalProof (dy.senc tH kH)
-- | aenc {X: TermSet} {t: Term} {k: Name} {tH: dy X t} {kH: dy X (Term.key (Key.pub k))} (tN: normalProof tH) (kN: normalProof kH): normalProof (dy.aenc tH kH)

@[simp]
def isNormal {X: TermSet} {t: Term} (proof: dy X t): Bool :=
    match proof with
    | dy.ax _ =>  true
    | dy.pk kH =>  (isNormal kH)
    | dy.splitL splitH =>            
                    match splitH with
                    | dy.ax _ =>  true
                    | dy.splitL splitH =>  isNormal splitH 
                    | dy.splitR splitH =>  isNormal splitH
                    | dy.sdec kH encH =>  isNormal kH && isNormal encH
                    | dy.adec kH encH =>  isNormal kH && isNormal encH
                    | dy.pair _ _ =>  false
    | dy.splitR splitH =>            
                    match splitH with
                    | dy.ax _ =>  true
                    | dy.splitL splitH =>  isNormal splitH 
                    | dy.splitR splitH =>  isNormal splitH
                    | dy.sdec kH encH =>  isNormal kH && isNormal encH
                    | dy.adec kH encH =>  isNormal kH && isNormal encH
                    | dy.pair _ _ =>  false
    | dy.pair tH uH =>  isNormal tH && isNormal uH
    | dy.senc tH kH =>  isNormal tH && isNormal kH
    | dy.aenc tH kH =>  isNormal tH && isNormal kH
    | dy.sdec encH kH => isNormal kH &&
                      match encH with
                      | dy.ax _ =>  true
                      | dy.splitL splitH =>  isNormal splitH 
                      | dy.splitR splitH =>  isNormal splitH
                      | dy.sdec kH encH =>  isNormal kH && isNormal encH
                      | dy.adec kH encH =>  isNormal kH && isNormal encH
                      | dy.senc _ _ =>  false
    | dy.adec encH kH => isNormal kH &&
                      match encH with
                      | dy.ax _ =>  true
                      | dy.splitL splitH =>  isNormal splitH 
                      | dy.splitR splitH =>  isNormal splitH
                      | dy.sdec kH encH =>  isNormal kH && isNormal encH
                      | dy.adec kH encH =>  isNormal kH && isNormal encH
                      | dy.aenc _ _ =>  false
@[simp]
def dyProofMeasure {X: TermSet} {t: Term} (proof: dy X t): Nat := 
      1 +
      match proof with
      | dy.ax _ =>  1
      | dy.pk kH =>  dyProofMeasure kH
      | dy.splitL splitH =>  dyProofMeasure splitH
      | dy.splitR splitH =>  dyProofMeasure splitH
      | dy.pair tH uH =>  dyProofMeasure tH + dyProofMeasure uH
      | dy.senc tH kH =>   dyProofMeasure tH + dyProofMeasure kH
      | dy.aenc tH kH =>   dyProofMeasure tH + dyProofMeasure kH
      | dy.sdec encH kH =>  dyProofMeasure encH + dyProofMeasure kH
      | dy.adec encH kH =>  dyProofMeasure encH + dyProofMeasure kH

@[simp]
def dyProofRewrite {X: TermSet} {t: Term} (proof: dy X t): dy X t :=
  match proof with
  | dy.splitL splitH =>
              match splitH with
              | dy.pair uH _ => uH
              | _ => proof
  | dy.splitR splitH =>
              match splitH with
              | dy.pair _ tH => tH
              | _ => proof
  | dy.sdec encH _ =>
              match encH with
              | dy.senc  tH _ => tH
              | _ => proof
  | dy.adec encH _ =>
              match encH with
              | dy.aenc  tH _ => tH
              | _ => proof
  | _ => proof

@[simp]
lemma dyProofRewriteSmaller: ∀ {X: TermSet} {t: Term} (proof: dy X t), 
  dyProofMeasure (dyProofRewrite proof) ≤ dyProofMeasure proof :=
  by
    intros X t proof
    cases proof with
    | splitL splitH  => 
             simp
             cases splitH with
             | pair tH uH => 
                    simp
                    omega
             | _ => simp
    
    | splitR splitH  => 
             simp
             cases splitH with
             | pair tH uH => 
                    simp
                    omega
             | _ => simp
    | sdec encH  _ => 
                simp
                cases encH with
                | senc _ _ => simp
                              omega
                | _ => simp
    | adec encH  _ => 
                simp
                cases encH with
                | aenc _ _ => simp
                              omega
                | _ => simp
    | _ => simp

@[simp]
def recursiveDyProofRewriter {X: TermSet} {t: Term} (p: dy X t) : dy X t :=
    match p with
    | dy.ax inH => dyProofRewrite (dy.ax inH)
    | dy.pk kH => dyProofRewrite (  dy.pk (recursiveDyProofRewriter kH))
    | dy.splitL splitH => dyProofRewrite ( dy.splitL (recursiveDyProofRewriter splitH))
    | dy.splitR splitH => dyProofRewrite ( dy.splitR (recursiveDyProofRewriter splitH))
    | dy.pair tH uH => dyProofRewrite (  dy.pair (recursiveDyProofRewriter tH) (recursiveDyProofRewriter uH))
    | dy.senc tH kH => dyProofRewrite (  dy.senc (recursiveDyProofRewriter tH) (recursiveDyProofRewriter kH)) 
    | dy.aenc tH kH => dyProofRewrite (  dy.aenc (recursiveDyProofRewriter tH) (recursiveDyProofRewriter kH))
    | dy.sdec encH kH => dyProofRewrite ( dy.sdec (recursiveDyProofRewriter encH) (recursiveDyProofRewriter kH))
    | dy.adec encH kH => dyProofRewrite ( dy.adec (recursiveDyProofRewriter encH) (recursiveDyProofRewriter kH))
@[simp]
def repeat_apply {A: Type} : Nat → (A → A) → A → A
| 0 => fun _ a => a 
| n + 1 => fun f a => f (repeat_apply n f a)

lemma repeatRight: ∀ {A: Type} (n: Nat) (f: A -> A) (a: A), repeat_apply (n + 1) f a = repeat_apply n f (f a) :=
  by
    intros A n f
    induction n with
    | zero => 
           intros a
           simp
    | succ n iHn =>
           intros a
           simp
           simp at iHn
           rw [iHn]
         

theorem rewriterFixpoint: ∀ {X: TermSet} {t: Term} (p: dy X t),∃ (n: Nat), repeat_apply n recursiveDyProofRewriter p = 
repeat_apply (n + 1) recursiveDyProofRewriter p :=
  by
    intros X t p
    induction p with
    | ax inH =>
         apply Exists.intro 0
         simp

    | pk kH kH_iH =>
         cases kH_iH with
         | intro x iHx =>
           rw [repeatRight] at iHx
           apply Exists.intro x
           rw [repeatRight]
           simp
           sorry
    
         -- cases kH_iH with
         -- | intro x xH =>
         --   apply Exists.intro (x + 1)
         --   rw [repeatRight, repeatRight]
         --   simp
         --   simp at xH
         --   sorry
    | splitL splitH splitH_ih =>
             simp
             sorry
    | _ => sorry
-- theorem rewriterNormaliser: ∀ {X: TermSet} {t: Term} (p: dy X t), isNormal (recursiveDyProofRewriter p) = true :=
--   by
--     intros X t p
--     induction p with
--     | ax inH => 
--          simp
--     | pk kH kH_ih =>
--              simp
--              assumption
--     | splitL splitH splitH_ih =>
--              simp
--              cases eqn : (recursiveDyProofRewriter splitH)  with    
--              | pair tH uH => 
--                     rw [eqn] at splitH_ih
--                     simp
--                     simp at splitH_ih
--                     cases splitH_ih with
--                     | intro left right => assumption
--              | ax inH =>
--                     simp
--              | splitL splitH =>
--                     rw [eqn] at splitH_ih
--                     simp
--                     unfold isNormal at splitH_ih
--                     simp at splitH_ih
    
--     sorry
