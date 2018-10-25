/*
 * Project1: NiceBook
 * NiceBook: Operations
 */
module NiceBook/NiceBookOp
open NiceBook/NiceBookBasic
open NiceBook/NiceBookPrivacy

// Make sure all instances are within the invariants
fact {
	all n:SocialNetwork | invariants[n]
}

// -------- Start: Operations -------
pred networkOp[n,n':SocialNetwork] {
	n'.users = n.users
	n'.friends = n.friends
}

pred is_naked[c:Content, n:SocialNetwork] {
	// can only add an independent content with no tags
	// no comment
	// not existed in the network
	no get_tags[c]
	no comment:Comment | comment.attached = c
	c not in User.(n.contents)
}

pred uploadPhoto[n,n':SocialNetwork,u:User,p:Photo] {
	// It is an independent photo
	no get_note_from_photo[p]	
	n'.contents = n.contents + u->p
}

pred uploadNote[n,n':SocialNetwork,u:User,note:Note] {
	all p:note.photos | is_naked[p, n] // photos are pure
	// add the photoes and note together
	n'.contents = n.contents + u->note + {a:User, c:Content | a = u and c in note.photos}
}

pred uploadComment[n,n':SocialNetwork,u:User,c:Comment] {
	// comment must be attached to a uploaded but unpublished content
	c.attached in get_upload_not_publish[n, u]
	n'.contents = n.contents + u->c
}

// O.1: upload
pred upload[n,n':SocialNetwork, u:User, c:Content] {
	networkOp[n,n']
	u in n.users and is_naked[c, n]		
	(c in Photo and uploadPhoto[n,n',u,c]) or // upload a photo
	(c in Note and uploadNote[n,n',u,c]) or // upload a note
	(c in Comment and uploadComment[n,n',u,c]) // upload a comment
}

run upload for 4

assert UploadPreserveInvariant {
	all n, n': SocialNetwork, u:User, c:Content |
		invariants[n] and upload[n,n',u,c] implies
		invariants[n']
}

check UploadPreserveInvariant for 7 but exactly 2 SocialNetwork
// end of O.1:upload

pred removeNote[n,n':SocialNetwork,u:User,note:Note] {
	// The photos, the comments and comments of photos not on the wall
	all p:note.photos | p not in u.wall.items
	all_comments[note] not in u.wall.items
	all p:note.photos | all_comments[p] not in u.wall.items
	// All the related contents not in the contents
	n'.contents = n.contents - 
			 {a:User, c:Content | a = u and 
			  c in (note + note.photos + all_comments[note] +
			  {c:Comment | some p:note.photos | c in all_comments[p]}
	)}
}

pred removePhoto[n,n':SocialNetwork, u:User, p:Photo] {
	// Photo no association with any note
	no get_note_from_photo[p]
	all_comments[p] not in u.wall.items
	n'.contents = n.contents - 
			  {m:User, c:Comment | m = u and c in (all_comments[p] + p)}
}

pred removeComment[n,n':SocialNetwork,u:User,c:Comment] {
	c.attached in get_upload_not_publish[n, u]
	n'.contents = n.contents - {m:User, o:Comment | 
					    m=u and o in all_comments[c]} - u->c
}

// begin of O.2: remove
pred remove[n,n':SocialNetwork, u:User, c:Content] {
	networkOp[n,n']
	// Pre-condition
	// not published
	u in n.users and u->c in n.contents and c not in u.wall.items
	// Post-condition
	(c in Photo and removePhoto[n,n',u,c]) or // remove a photo
	(c in Note and removeNote[n,n',u,c]) or
	(c in Comment and removeComment[n,n',u,c])
	
}

run remove for 4

assert RemovePreserveInvariant {
	all n, n':SocialNetwork, u:User, c:Content |
		invariants[n] and remove[n,n',u,c] implies
		invariants[n']
}

check RemovePreserveInvariant for 7 but exactly 2 SocialNetwork
// end of O.2 remove


// Global states in O.3 and O.4
pred promotePublish[n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content] {
	// Precodition
	u in n.users
	u.wall = w
	u' not in n.users
	// Postcondition
	u'.wall = w'
	n'.users = n.users - u + u'
	n'.contents = n.contents ++ u' -> c  // fine if c is new
	all u1 : u.(n.friends) | n'.friends = n.friends - u -> u1 + u' -> u1
	all u2 : (n.friends).u | n'.friends = n.friends - u2 -> u + u2 -> u'
}

// Local states in O.3
pred publishWall[w,w':Wall, c:Content] {
	w'.wallPrivacy = w.wallPrivacy
	// Publish to the wall
	w'.items = w.items + c  // TODO: everything related to c
}

// O.3: publish
pred publish[n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content] {
	// Precondition
	c not in w.items
	// B.8: Notes and photos from the user or its friends can be published
	c in u.(n.contents) + u.(n.friends).(n.contents)
	c in Note + Photo
	// Operations
	publishWall[w,w',c]
	promotePublish[n,n',u,u',w,w',c]
}

assert PublishPreserveInvariant {
	all n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content |
		invariants[n] and publish[n,n',u,u',w,w',c] implies
		invariants[n']
}

check PublishPreserveInvariant for 5 but exactly 2 SocialNetwork

// Local states in O.4
pred unpublishWall[w,w':Wall, c:Content] {
	w'.wallPrivacy = w.wallPrivacy
	// Unpublish to the wall
	w'.items = w.items - c  // TODO: everything related to c
}

// O.4: unpublish
pred unpublish[n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content] {
	// Precondition
	c in w.items
	// Operations
	unpublishWall[w,w',c]
	promotePublish[n,n',u,u',w,w',c]
}

assert UnpublishPreserveInvariant {
	all n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content |
		invariants[n] and publish[n,n',u,u',w,w',c] implies
		invariants[n']
}

check UnpublishPreserveInvariant for 2 but exactly 2 SocialNetwork

// O.5: addComment
pred addComment[n,n':SocialNetwork, u:User, c:Comment, x:Content] {
	// B.10: Own or visible content
	x in viewable[u,n]
	// User can control who can comment on their content
	x in commentable[u,n]
	networkOp[n,n']
	c not in User.(n.contents)
	// Add comment
	n'.contents = n.contents + u->c
	c.attached = x
}

assert AddPreservesInvariant {
	all n,n':SocialNetwork, u:User, c:Comment, x:Content |
		invariants[n] and addComment[n,n',u,c,x] implies
		invariants[n']	
}

check AddPreservesInvariant for 5

run addComment for 10

// Unchanged things in content while tagging
pred contentOp[c,c':Content] {
	c'.viewPrivacy = c.viewPrivacy
	c'.photos = c.photos
	c'.attached = c.attached
}

// O.6: addTag
pred addTag[n,n',n'':SocialNetwork, t:Tag, c,c':Content, er,ee,ee':User, w,w':Wall] {
	// Precondition
	t not in User.(n.contents).noteTags
	t not in User.(n.contents).photoTags
	c in User.(n.contents)
	c' not in User.(n.contents)
	er in n.users
	ee in n.users
	c in viewable[er,n]  // er can view c
	// Postcondition
	all u:((n.contents).c & n.users) | n'.contents = n.contents - u -> c + u -> c'
	// Add a tag to a photo or a note
	t.tagger = er
	t.taggee = ee
	((c in Note) and (c'.noteTags = c.noteTags + t)) or
	((c in Photo) and (c'.photoTags = c.photoTags + t))
	contentOp[c,c']
	// Automatically published onto ee's wall
	publish[n',n'',ee,ee',w,w',c']
}

assert AddTagPreservesInvariant {
	all n,n',n'':SocialNetwork, t:Tag, c,c':Content, er,ee,ee':User, w,w':Wall |
		(invariants[n] and addTag[n,n',n'',t,c,c',er,ee,ee',w,w']) implies
		(invariants[n'] and invariants[n''])
}
check AddTagPreservesInvariant for 5

// O.7: removeTag
pred removeTag[n,n':SocialNetwork, t:Tag] {}

// --------- End: Operations --------
