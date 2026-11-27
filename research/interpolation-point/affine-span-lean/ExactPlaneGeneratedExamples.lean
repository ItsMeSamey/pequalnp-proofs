import ExactPlaneGeneratedWitness
open ExactPlaneGeneratedDecision ExactPlaneResidualPivots
private def p (_ : Fin 3) : Fin 0→ZMod 2 := Fin.elim0
private def tags (_ : Fin 3) : Plane := 0
private def heights (i : Fin 3) : Plane := if i=2 then (0,1) else (1,0)
#eval (ExactPlaneGeneratedDecision.decide p tags heights).map (fun x=>x.2.card)
#eval (ExactPlaneGeneratedDecision.decide p tags (fun _=>(1,0))).isSome
#eval (ExactPlaneConstructedRows.generate 2 0).length
-- At m=2, degree two suffices. The four possible rows all occur.
#eval ((ExactPlaneConstructedRows.generate 2 0).eraseDups).length
