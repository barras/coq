theories/Logic/Eqdep_dec.vo: theories/Logic/Eqdep_dec.v
theories/Logic/Eqdep.vo: theories/Logic/Eqdep.v
theories/Logic/Classical_Type.vo: theories/Logic/Classical_Type.v theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Type.vo
theories/Logic/Classical_Prop.vo: theories/Logic/Classical_Prop.v
theories/Logic/Classical_Pred_Type.vo: theories/Logic/Classical_Pred_Type.v theories/Logic/Classical_Prop.vo
theories/Logic/Classical_Pred_Set.vo: theories/Logic/Classical_Pred_Set.v theories/Logic/Classical_Prop.vo
theories/Logic/Classical.vo: theories/Logic/Classical.v theories/Logic/Classical_Prop.vo theories/Logic/Classical_Pred_Set.vo
theories/Init/Wf.vo: theories/Init/Wf.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo
theories/Init/SpecifSyntax.vo: theories/Init/SpecifSyntax.v theories/Init/LogicSyntax.vo theories/Init/Specif.vo
theories/Init/Specif.vo: theories/Init/Specif.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo
theories/Init/Prelude.vo: theories/Init/Prelude.v theories/Init/Datatypes.vo theories/Init/DatatypesSyntax.vo theories/Init/Logic.vo theories/Init/LogicSyntax.vo theories/Init/Specif.vo theories/Init/SpecifSyntax.vo theories/Init/Peano.vo theories/Init/Wf.vo
theories/Init/Peano.vo: theories/Init/Peano.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo theories/Init/Datatypes.vo
theories/Init/Logic_TypeSyntax.vo: theories/Init/Logic_TypeSyntax.v theories/Init/Logic_Type.vo
theories/Init/Logic_Type.vo: theories/Init/Logic_Type.v theories/Init/Logic.vo theories/Init/LogicSyntax.vo
theories/Init/LogicSyntax.vo: theories/Init/LogicSyntax.v theories/Init/Logic.vo
theories/Init/Logic.vo: theories/Init/Logic.v theories/Init/Datatypes.vo
theories/Init/DatatypesSyntax.vo: theories/Init/DatatypesSyntax.v theories/Init/Datatypes.vo
theories/Init/Datatypes.vo: theories/Init/Datatypes.v
theories/Bool/Zerob.vo: theories/Bool/Zerob.v theories/Arith/Arith.vo theories/Bool/Bool.vo
theories/Bool/Sumbool.vo: theories/Bool/Sumbool.v
theories/Bool/IfProp.vo: theories/Bool/IfProp.v theories/Bool/Bool.vo
theories/Bool/DecBool.vo: theories/Bool/DecBool.v
theories/Bool/Bool.vo: theories/Bool/Bool.v
theories/Arith/Wf_nat.vo: theories/Arith/Wf_nat.v theories/Arith/Lt.vo
theories/Arith/Plus.vo: theories/Arith/Plus.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Peano_dec.vo: theories/Arith/Peano_dec.v
theories/Arith/Mult.vo: theories/Arith/Mult.v theories/Arith/Plus.vo theories/Arith/Minus.vo
theories/Arith/Minus.vo: theories/Arith/Minus.v theories/Arith/Lt.vo theories/Arith/Le.vo
theories/Arith/Min.vo: theories/Arith/Min.v theories/Arith/Arith.vo
theories/Arith/Lt.vo: theories/Arith/Lt.v theories/Arith/Le.vo
theories/Arith/Le.vo: theories/Arith/Le.v
theories/Arith/Gt.vo: theories/Arith/Gt.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo
theories/Arith/Even.vo: theories/Arith/Even.v
theories/Arith/Euclid_proof.vo: theories/Arith/Euclid_proof.v theories/Arith/Euclid_def.vo theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo
theories/Arith/Euclid_def.vo: theories/Arith/Euclid_def.v theories/Arith/Mult.vo
theories/Arith/EqNat.vo: theories/Arith/EqNat.v
theories/Arith/Div2.vo: theories/Arith/Div2.v theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Compare_dec.vo theories/Arith/Even.vo
theories/Arith/Div.vo: theories/Arith/Div.v theories/Arith/Le.vo theories/Arith/Euclid_def.vo theories/Arith/Compare_dec.vo
theories/Arith/Compare_dec.vo: theories/Arith/Compare_dec.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Compare.vo: theories/Arith/Compare.v theories/Arith/Arith.vo theories/Arith/Peano_dec.vo theories/Arith/Compare_dec.vo theories/Arith/Wf_nat.vo theories/Arith/Min.vo
theories/Arith/Between.vo: theories/Arith/Between.v theories/Arith/Le.vo theories/Arith/Lt.vo
theories/Arith/Arith.vo: theories/Arith/Arith.v theories/Arith/Le.vo theories/Arith/Lt.vo theories/Arith/Plus.vo theories/Arith/Gt.vo theories/Arith/Minus.vo theories/Arith/Mult.vo theories/Arith/Between.vo
test-suite/bench/lists_100.vo: test-suite/bench/lists_100.v
test-suite/bench/lists-100.vo: test-suite/bench/lists-100.v
tactics/Equality.vo: tactics/Equality.v
syntax/PPTactic.vo: syntax/PPTactic.v
syntax/PPConstr.vo: syntax/PPConstr.v
syntax/PPCases.vo: syntax/PPCases.v
syntax/MakeBare.vo: syntax/MakeBare.v
states/MakeInitial.vo: states/MakeInitial.v theories/Init/Prelude.vo theories/Init/Logic_Type.vo theories/Init/Logic_TypeSyntax.vo tactics/Equality.vo
