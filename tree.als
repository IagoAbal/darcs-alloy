
module tree

/**
	Model of repository tree.

	We could define a tree as a directory under version control.
	This module is intended to model the API provided by Darcs.IO module 
	through the ReadableRepository and WritableRepository type classes.

	Warning: This tree model is not fully functional due to Alloy limitations,
	              see Rename operation for more details.
*/


open util/integer
open util/sequniv



////////  Path
--
-- The offered API is completely based on paths,  as opposed to traditional APIs
-- which use the concept of handle to operate over filesystem objects.
--
-- We have described paths following the ideas of the hashed-storage Haskell package, 
-- though we forbid paths that point to the root, since operations are only defined for child tree items.
-- A Haskell implementation could easily enforce the same restriction by the use of non-null lists.
-- See http://hackage.haskell.org/packages/archive/hashed-storage/0.5.4/doc/html/Storage-Hashed-AnchoredPath.html
--

sig Name {}

sig Path {
	parent : lone Path,
	name : one Name
}

fact Paths_Are_Acyclic {
	all p : Path | p not in p.ancestor
}

fact CanonizePath {
	no disj p1, p2 : Path | p1.parent = p2.parent and p1.name = p2.name
}

////////  Path //////// Util

fun mkPath[base : Path, n : Name] : Path {
	{ p : Path | p.parent = base and p.name = n }
}

fun ancestor[p : Path] : set Path {
	p.^parent
}

pred isPrefix[p, q : Path] {
	 p in (q + q.ancestor)
}

//////// Tree

sig Line {}

sig Tree {
	Dirs  : set Path,
	Files : set Path,
	content : Path -> (seq Line)
}

--
-- Trees must be canonized, otherwise some operations over trees won't be simple/injective.
--
fact CanonizeTree {
	no disj t1, t2 : Tree | t1.Dirs = t2.Dirs and t1.Files = t2.Files and t1.content = t2.content
}

pred Inv[t : Tree] {
	no (t.Dirs & t.Files)
	all x : t.Items | x.parent in t.Dirs
	t.content in t.Files -> (seq Line)
}

run Inv

pred TreeInv_Consistent_Nontrivial[t : Tree] {
	t.Inv
	--
	#t.Items >= 3
}

run TreeInv_Consistent_Nontrivial for 5 but exactly 1 Tree

//////// Tree //////// Util

pred isEmpty[t : Tree] {
	no t.Items
}

fun Items[t : Tree] : set Path {
	t.Dirs + t.Files
}

fun children[t : Tree, d : Path] : set Path {
	t.Items & parent.d
}

pred isEmptyDir[t : Tree, d : Path] {
	d in t.Dirs
	no t.children[d]
}

fun readFile[t : Tree, f : Path] : seq Line {
	t.content[f]
}

//////// Tree //////// Create a directory

pred CreateDir[ t : Tree, d : Path, t' : Tree ] {
	-- PRE
	d not in t.Items
	d.parent in t.Dirs

	-- CHANGE
	t'.Dirs = t.Dirs + d

	-- KEEP
	t'.Files = t.Files
	t'.content = t.content
}

--- > Consistency and safety

pred CreateDir_Consistent[t : Tree, p : Path, t' : Tree] {
--	#t.items > 2
	t.Inv
	CreateDir[t,p,t']
}

run CreateDir_Consistent for 4 but 2 Tree

assert CreateDir_Safe {
	all t, t' : Tree, p : Path |
		t.Inv and CreateDir[t,p,t'] => t'.Inv
}

check CreateDir_Safe for 5

//////// Tree //////// Remove a directory

pred RemoveDir[t : Tree, d : Path, t' : Tree] {
	-- PRE
	d in t.Dirs
	t.isEmptyDir[d]	// Only empty directories could be removed

	-- CHANGE
	t'.Dirs = t.Dirs - d

	-- KEEP
	t'.Files = t.Files
	t'.content = t.content
}

--- > Consistency and safety

pred RemoveDir_Consistent[t : Tree, p : Path, t' : Tree] {
--	#t.items > 2
	t.Inv
	RemoveDir[t,p,t']
}

run RemoveDir_Consistent for 4 but 2 Tree

assert RemoveDir_Safe {
	all t, t' : Tree, p : Path |
		t.Inv and RemoveDir[t,p,t'] => t'.Inv
}

check RemoveDir_Safe for 5

//////// Tree //////// Create a file

pred CreateFile[t : Tree,  f : Path, t' : Tree] {
	-- PRE
	f.parent in t.Dirs
	f not in t.Items

	-- CHANGE
	t'.Files = t.Files + f

	-- KEEP
	t'.Dirs = t.Dirs
	t'.content = t.content
}

--- > Consistency and safety

pred CreateFile_Consistent[t : Tree,  p : Path, t' : Tree] {
	t.Inv
	CreateFile[t,p,t']
}

run CreateFile_Consistent for 4 but 2 Tree

assert CreateFile_Safe {
	all t, t' : Tree,  p : Path |
		t.Inv and CreateFile[t,p,t'] =>t'.Inv
}
check CreateFile_Safe for 5

//////// Tree //////// Remove a file

pred RemoveFile[t : Tree, f : Path, t' : Tree] {
	-- PRE
	f in t.Files

	-- CHANGE
	t'.Files = t.Files - f
	t'.content = t.content - (f -> Int -> Line)

	-- KEEP
	t'.Dirs = t.Dirs
}

--- > Consistency and safety

pred RemoveFile_Consistent[t : Tree, p : Path, t' : Tree] {
	t.Inv
	RemoveFile[t,p,t']
}

run RemoveFile_Consistent for 4 but 2 Tree

assert RemoveFile_Safe {
	all t, t' : Tree, p : Path |
		t.Inv and RemoveFile[t,p,t'] => t'.Inv
}

check RemoveFile_Safe for 5

//////// Tree //////// Write file

pred WriteFile[t : Tree,  f : Path, text : seq Line, t' : Tree] {
	-- PRE
	f in t.Files

	-- CHANGE
	t'.content = t.content - (f -> Int -> Line) + (f -> text)

	-- KEEP
	t'.Dirs = t.Dirs
	t'.Files = t.Files
}

--- > Consistency and safety

pred WriteFile_Consistent[t : Tree,  f : Path, text : seq Line, t' : Tree] {
	t.Inv
	WriteFile[t,f,text,t']
}

run WriteFile_Consistent for 4 but 2 Tree

pred WriteFile_Consistent_Nontrivial[t : Tree, f : Path, text : seq Line, t' : Tree] {
	t.Inv
	WriteFile[t,f,text,t']
	--
	t.content != t'.content
	some f.parent
}

run WriteFile_Consistent_Nontrivial for 4 but 2 Tree

assert WriteFile_Safe {
	all t, t' : Tree, p : Path, text : seq Line |
			t.Inv and WriteFile[t,p,text,t'] => t'.Inv
}

check WriteFile_Safe

//////// Tree //////// Rename

pred Rename[ t : Tree, src : Path, dest : Path, t' : Tree ] {
	-- PRE
	src in t.Items
	dest.parent in t.Dirs
	dest not in t.Items
	// We cannot move a directory into itself or one of its subdirectories
	// Example: /home -> /home/user
	not isPrefix[src, dest.parent]
	-- When renaming directories we also need to rename recursively all its descendants,
	-- which makes the specification of a fully functional Rename operation far from trivial
	-- (perhaps impossible) since Alloy lacks recursion.
	-- We have decided to limit Rename to be applicable to a directory only in the case
	-- its subtree is flat. We think this simpler Rename should be enough to find errors related
	-- to renaming of directories.
	no (t.Items & parent.parent.src)
	

	-- CHANGE
	let rename = { p, p' : Path | p = src => p' = dest
				 							else p.parent = src => (p'.parent = dest and p'.name = p.name)
				 							else p' = p }
	{
		t'.Files = rename[t.Files]
		t'.Dirs = rename[t.Dirs]
		#t'.Items = #t.Items		// We need to force all new paths to exist

		t'.content = (~rename).(t.content)
	}
}

--- > Consistency and safety

pred Rename_Consistent[t : Tree, src : Path, dest : Path, t' : Tree] {
	t.Inv
	Rename[t,src,dest,t']
}

run Rename_Consistent for 4

pred Rename_Consistent_NonemptyDir[t : Tree, src : Path, dest : Path, t' : Tree] {
	t.Inv
	Rename[t,src,dest,t']
	--
	src != dest
	some (t.Items & parent.src)
	some t.content
}

run Rename_Consistent_NonemptyDir for 7

assert Rename_Safe {
	all t, t' : Tree, src, dest : Path |
		t.Inv and Rename[t,src,dest,t'] => t'.Inv
}

check Rename_Safe for 6

assert Rename_SrcEqDestDoesNothing {
	all t, t' : Tree, src : Path |
		t.Inv and Rename[t,src,src,t'] => t = t'
}

check Rename_SrcEqDestDoesNothing for 6
