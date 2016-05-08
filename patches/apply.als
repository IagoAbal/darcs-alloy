
module patches/apply

/**
	Application of patches over a tree.
*/


open tree
open patches/types



//////// Apply

pred Apply[t : Tree, p : Patch, t' : Tree] {
	ApplyDirpatch[t,p,t'] or ApplyFilepatch[t,p,t'] or ApplyMove[t,p,t']
}

--- > Consitency and safety

pred Apply_Consistent[t : Tree, p : Patch, t' : Tree] {
	t.Inv and p.Inv
	Apply[t,p,t']
}

run Apply_Consistent for 4 but exactly 1 Patch

assert Apply_Safe {
	all t, t' : Tree, p : Patch |
		t.Inv and p.Inv and Apply[t,p,t'] => t'.Inv
}

check Apply_Safe for 5

--- > Applicability

pred isApplicableTo[p : Patch, t : Tree] {
	p.Inv and t.Inv
	some t' : Tree | Apply[t,p,t']
}

run isApplicableTo for 4 but exactly 1 Patch, 2 Tree

pred isSensible[p : Patch] {
	some t : Tree | p.isApplicableTo[t]
}

run isSensible

//////// Apply //////// Sequential
-- 
-- Two patches are sequential if they can be applied in sequence.
-- It just states that the composition of p and q is sensible (i.e. non bottom effect).
--

pred sequential[p, q : Patch] {
	some t1, t2, t3 : Tree | t1.Inv and Apply[t1,p,t2] and Apply[t2,q,t3]
}

//////// Apply //////// Effect
--
-- We could view a patch as an injective partial function going from Tree to Tree.
-- This view is often referred in the literature as the effect of a patch.
--
-- Note that if we compose the effect of two patches we get the effect of
-- their composition, and so test if a pair of patches are sequential is equivalent
-- to test if their composed effect is non-empty.
--

fun Effect[p : Patch] : Tree -> Tree {
	{ t1, t2 : Tree | t1.Inv and Apply[t1,p,t2] }
}

assert Effect_SimpleAndInjective {
	all p : Patch | p.Inv => p.Effect in Tree lone -> lone Tree
}

check Effect_SimpleAndInjective

//////// Apply //////// Theorems

-- Can't be verified with Alloy: universe is not saturated enough
//assert EveryPatchIsSensible {
//	all p : Patch | p.Inv => some t : Tree | p.isApplicableTo[t]
//}
//check EveryPatchIsSensible for 4 but exactly 1 Patch, 2 Tree

//////// Apply //////// Directory patch

pred ApplyDirpatch[t : Tree, dp : DirPatch, t' : Tree] {
	dp in DirPatch
	ApplyAdddir[t,dp,t'] or ApplyRmdir[t,dp,t']
}

//////// Apply //////// Directory patch //////// Add directory

pred ApplyAdddir[t : Tree, addd : Adddir, t' : Tree] {
	addd in Adddir
	CreateDir[t,addd.path,t']
}

--- > Consistency & safety

pred ApplyAdddir_Consistent[t : Tree, addd : Adddir, t' : Tree] {
	t.Inv
	ApplyAdddir[t,addd,t']
}

run ApplyAdddir_Consistent for 4 but exactly 1 Patch, 2 Tree

assert ApplyAdddir_Safe {
	all t, t' : Tree, addd : Adddir |
		t.Inv and ApplyAdddir[t,addd,t'] => t'.Inv
}

check ApplyAdddir_Safe for 4


//////// Apply //////// Directory patch //////// Remove directory

pred ApplyRmdir[t : Tree, rmd : Rmdir, t' : Tree] {
	rmd in Rmdir
	RemoveDir[t,rmd.path,t']
}

--- > Consistency & safety

pred ApplyRmdir_Consistent[t : Tree, rmd : Rmdir, t' : Tree] {
	t.Inv
	ApplyRmdir[t,rmd,t']
}

run ApplyRmdir_Consistent for 4 but exactly 1 Patch, 2 Tree

assert ApplyRmdir_Safe {
	all t, t' : Tree, rmd : Rmdir |
		t.Inv and ApplyRmdir[t,rmd,t'] => t'.Inv
}

check ApplyRmdir_Safe for 4

//////// Apply //////// File patch

pred ApplyFilepatch[t : Tree, fp : FilePatch, t' : Tree] {
	fp in FilePatch
	ApplyHunk[t,fp,t'] or ApplyAddfile[t,fp,t'] or ApplyRmfile[t,fp,t']
}

//////// Apply //////// File patch //////// Add a file

pred ApplyAddfile[t : Tree, addf : Addfile, t' : Tree] {
	addf in Addfile
	CreateFile[t,addf.path,t']
}

--- > Consistency & safety

pred ApplyAddfile_Consistent[t : Tree, addf : Addfile, t' : Tree] {
	t.Inv
	ApplyAddfile[t,addf,t']
}

run ApplyAddfile_Consistent for 4 but exactly 1 Patch, 2 Tree

assert ApplyAddfile_Safe {
	all t, t' : Tree, addf : Addfile |
		t.Inv and ApplyAddfile[t,addf,t'] => t'.Inv
}

check ApplyAddfile_Safe for 4

//////// Apply //////// File patch //////// Remove a file

pred ApplyRmfile[t : Tree, rmf : Rmfile, t' : Tree] {
	-- PRE
	rmf in Rmfile
	no t.content[rmf.path]

	RemoveFile[t,rmf.path,t']
}

--- > Consistency & safety

pred ApplyRmfile_Consistent[t : Tree, rmf : Rmfile, t' : Tree] {
	t.Inv
	ApplyRmfile[t,rmf,t']
}

run ApplyRmfile_Consistent for 4 but exactly 1 Patch, 2 Tree

assert ApplyRmfile_Safe {
	all t, t' : Tree, rmf : Rmfile |
		t.Inv and ApplyRmfile[t,rmf,t'] => t'.Inv
}

check ApplyRmfile_Safe for 4

//////// Apply //////// File patch //////// Hunk

pred ApplyHunk[t : Tree, h : Hunk, t' : Tree] {
	-- PRE
	h in Hunk
	h.path in t.Files
	let text = t.readFile[h.path],
		 old_next = h.line.add[#h.old], new_next = h.line.add[#h.new], 
		 old_end = old_next.prev, new_end = new_next.prev
	{
		old_end < #text and h.old = text.subseq[h.line,old_end]	// old content is right
		pos[h.ldelta] and pos[#text] => text.lastIdx.add[h.ldelta] in seq/Int		// respect file size limit

		let text' = t'.readFile[h.path] {
			WriteFile[t,h.path,text',t']	// nothing but the content of the file pointed by h.path is changed

			-- CHANGE
			#text' = (#text).add[h.ldelta]
			text'.subseq[h.line,new_end] = h.new

			-- KEEP
			text'.subseq[0,h.line.prev] = text.subseq[0,h.line.prev]	// same prefix
			text'.subseq[new_next,text'.lastIdx] = text.subseq[old_next,text.lastIdx]	// same rest
		}
	}
}

--- > Consistency & safety

pred ApplyHunk_Consistent[t : Tree, h : Hunk, t' : Tree] {
	t.Inv and h.HunkInv
	ApplyHunk[t,h,t']
}

run ApplyHunk_Consistent for 4 but 2 Tree, exactly 1 Patch, 5 Path

assert ApplyHunk_Safe {
	all t, t' : Tree, h : Hunk |
		t.Inv and h.HunkInv and ApplyHunk[t,h,t'] => t'.Inv
}

check ApplyHunk_Safe for 5

//////// Apply //////// Move patch

pred ApplyMove[t : Tree, mv : Move, t' : Tree] {
	mv in Move
	Rename[t,mv.source,mv.dest,t']
}

--- > Consistency & safety

pred ApplyMove_Consistent[t : Tree, mv : Move, t' : Tree] {
	t.Inv and mv.MoveInv
	ApplyMove[t,mv,t']
}

run ApplyMove_Consistent for 4 but exactly 1 Patch, 2 Tree

pred ApplyMove_Consistent_NonemptyDir[t : Tree, mv : Move, t' : Tree] {
	t.Inv and mv.MoveInv
	some (t.Items & parent.(mv.source))
	ApplyMove[t,mv,t']
}

run ApplyMove_Consistent_NonemptyDir for 4 but exactly 1 Patch, 2 Tree

assert ApplyMove_Safe {
	all t, t' : Tree, mv : Move |
		t.Inv and mv.MoveInv and ApplyMove[t,mv,t'] => t'.Inv
}

check ApplyMove_Safe for 6



