
module patches/invert

/**
	Inversion of patches.
*/


open tree
open patches/types
open patches/apply



//////// Invert

pred Invert[p, p_inv : Patch] {
	InvertDirpatch[p, p_inv] or InvertFilepatch[p, p_inv] or InvertMove[p, p_inv]
}

pred Invert_Consistent[p, p_inv : Patch] {
	p.Inv
	p.Invert[p_inv]
}

run Invert_Consistent for 4 but 2 Patch

assert Invert_Safe {
	all p, p_inv : Patch |
		p.Inv and p.Invert[p_inv] => p_inv.Inv
}

check Invert_Safe for 4

//////// Invert //////// Properties & Theorems

-- Can't be proven with Alloy: universe is not saturated enough
//assert EveryPatchIsInvertible {
//	all p : Patch | p.Inv => some p_inv : Patch | p.Invert[p_inv]
//}
//check EveryPatchIsInvertible

assert Invert_Converse {
	all p, p_inv : Patch | p.Invert[p_inv] => p_inv.Effect = ~(p.Effect)
}
check Invert_Converse for 3 -- 4, 5 (takes a lot)

assert Invert_Simple {
	all p, p_inv, p_inv' : Patch | p.Invert[p_inv] and p.Invert[p_inv'] => p_inv' = p_inv
}
check Invert_Simple for 4

assert Invert_Injective {
	all p, p', p_inv : Patch | p.Invert[p_inv] and p'.Invert[p_inv] => p = p'
}
check Invert_Injective for 4

assert Invert_Rollback {
	all p, p_inv  : Patch, t, t' : Tree |
		(p.Inv and t.Inv and Apply[t,p,t'] and p.Invert[p_inv])  => Apply[t',p_inv,t]
}
check Invert_Rollback for 4

-- From Judah Jacobson formalization. 
assert Invert_Identity {
	all p, p_inv, p_inv_inv : Patch | 
		p.Inv and p.Invert[p_inv] and p_inv.Invert[p_inv_inv] => p = p_inv_inv
}
check Invert_Identity for 4

-- Darcs User Manual said this is a theorem that should hold from 
-- previous assertions, but we test it anyway because we are not 
-- completely sure that this is true for the syntactic invert operation 
-- we are specifying.
-- On the other hand Judah Jacobson formalization seems to say
-- that this is a property the implementation must ensure.
assert Invert_Composition {
	all p, q, q_inv, p_inv : Patch, t1, t2, t3 : Tree |
		(p.Inv and q.Inv and t1.Inv and t3.Inv and
			p.Invert[p_inv] and q.Invert[q_inv]) =>
					((Apply[t1,p,t2] and Apply[t2,q,t3]) <=> (Apply[t3,q_inv,t2] and Apply[t2,p_inv,t1]))
}
check Invert_Composition for 4 but 3 Tree

//////// Invert //////// Dir patch

pred InvertDirpatch[dp, dp_inv : DirPatch] {
	dp in DirPatch and dp_inv in DirPatch
	dp.InvertAdddir[dp_inv] or dp.InvertRmdir[dp_inv]
}

pred InvertAdddir[p : Adddir, p_inv : Rmdir] {
	p in Adddir and p_inv in Rmdir
	p_inv.path = p.path
}

run InvertAdddir // Consistency

pred InvertRmdir[p : Rmdir, p_inv : Adddir] {
	p in Rmdir and p_inv in Adddir
	p_inv.path = p.path
}

run InvertRmdir // Consistency

//////// Invert //////// File patch

pred InvertFilepatch[fp, fp_inv : FilePatch] {
	fp in FilePatch and fp_inv in FilePatch
	fp.InvertAddfile[fp_inv] or fp.InvertRmfile[fp_inv] or fp.InvertHunk[fp_inv]
}

pred InvertAddfile[p : Addfile, p_inv : Rmfile] {
	p in Addfile and p_inv in Rmfile
	p_inv.path = p.path
}

run InvertAddfile // Consistency

pred InvertRmfile[p : Rmfile, p_inv : Addfile] {
	p in Rmfile and p_inv in Addfile
	p_inv.path = p.path
}

run InvertRmfile // Consistency

//////// Invert //////// File patch //////// Hunk

pred InvertHunk[h, h_inv : Hunk] {
	h in Hunk and h_inv in Hunk
	h_inv.path = h.path
	h_inv.line = h.line
	h_inv.old = h.new
	h_inv.new = h.old
}

--- > Consistency & safety

pred InvertHunk_Consistent[h, h_inv : Hunk] {
	h.HunkInv
	h.InvertHunk[h_inv]
}

run InvertHunk_Consistent for 4 but 2 Patch

assert InvertHunk_Safe {
	all h, h_inv : Hunk | h.HunkInv and h.InvertHunk[h_inv] => h_inv.HunkInv
}

check InvertHunk_Safe for 4

//////// Invert //////// Move

pred InvertMove[mv, mv_inv : Move] {
	mv in Move and mv_inv in Move
	mv_inv.source = mv.dest
	mv_inv.dest = mv.source
}

--- > Consistency & safety

pred InvertMove_Consistent[mv, mv_inv : Move] {
	mv.MoveInv
	mv.InvertMove[mv_inv]
}

run InvertMove_Consistent for 4 but 2 Patch

assert InvertMove_Safe {
	all mv, mv_inv : Move |
		mv.MoveInv and mv.InvertMove[mv_inv] => mv_inv.MoveInv
}

check InvertMove_Safe for 4

