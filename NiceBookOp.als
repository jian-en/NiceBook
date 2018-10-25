/*
 *NiceBook
 *
 */
module NiceBook/NiceBookOp
open NiceBook/NiceBookBasic
open NiceBook/NiceBookPrivacy

fact {
	all n:SocialNetwork | invariants[n]
}

// -------- Start: Operations -------
// A.2: The social network has a fixed set of users/friendships
pred networkOp[n,n':SocialNetwork] {
	n'.users = n.users
	n'.friends = n.friends
}

// c is a pure content, either Note or Photo
pred is_naked[c:Content] {
	no get_tags[c]
	no comment:Comment | comment.attached = c
	no note:Note | c in note.photos
}

// O.1: upload
pred upload[n,n':SocialNetwork, u:User, c:Content] {
	networkOp[n,n']	
	// Precondition: c not exist and u exists in User
	c not in User.(n.contents) and u in n.users
	is_naked[c]
	// Postcondition
	n'.contents = n.contents + u->c
}

run upload for 3

assert UploadPreserveInvariant {
	all n, n': SocialNetwork, u:User, c:Content |
		invariants[n] and upload[n,n',u,c] implies
		invariants[n']
}

check UploadPreserveInvariant for 5 but exactly 2 SocialNetwork


// O.2: remove
pred remove[n,n':SocialNetwork, u:User, c:Content] {
	networkOp[n,n']
	// Pre-condition:
	// u does have the c
	u->c in n.contents and u in n.users
	#(get_related[c] & u.wall.items) = 0
	// Post-condition
	
	n'.contents = n.contents - {i:User, m:Content | i = u and m in get_related[c]}
}

run remove for 3

assert RemovePreserveInvariant {
	all n, n': SocialNetwork, u:User, c:Content |
		invariants[n] and remove[n,n',u,c] implies
		invariants[n']
}

check RemovePreserveInvariant for 5 but exactly 2 SocialNetwork


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

run publish for 3
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

run unpublish for 3
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
	c.viewPrivacy = x.viewPrivacy
}

assert AddPreservesInvariant {
	all n,n':SocialNetwork, u:User, c:Comment, x:Content |
		invariants[n] and addComment[n,n',u,c,x] implies
		invariants[n']	
}

check AddPreservesInvariant for 10

run AddComment {
	some n,n':SocialNetwork, u:User, c:Comment, x:Content | 
	invariants[n] and #n.users = 2 and addComment[n,n',u,c,x]
} for 10 

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
	// Automatically publish onto ee's wall
	publish[n',n'',ee,ee',w,w',c']
}

assert AddTagPreservesInvariant {
	all n,n',n'':SocialNetwork, t:Tag, c,c':Content, er,ee,ee':User, w,w':Wall |
		(invariants[n] and addTag[n,n',n'',t,c,c',er,ee,ee',w,w']) implies
		(invariants[n'] and invariants[n''])
}

run addTag for 3
check AddTagPreservesInvariant for 5

// O.7: removeTag
pred removeTag[n,n',n'':SocialNetwork, t:Tag, c,c':Content, ee,ee':User, w,w':Wall] {
	// Precondition
	c in User.(n.contents)
	c' not in User.(n.contents)
	t in c.noteTags + c.photoTags
	ee = t.taggee
	// Postcondition
	all u:((n.contents).c & n.users) | n'.contents = n.contents - u -> c + u -> c'
	// Remove a tag
	((c in Note) and (c'.noteTags = c.noteTags - t)) or
	((c in Photo) and (c'.photoTags = c.photoTags - t))
	contentOp[c,c']
	// Automatically unpublish from ee's wall
	unpublish[n',n'',ee,ee',w,w',c]
}

assert RemoveTagPreservesInvariant {
	all n,n',n'':SocialNetwork, t:Tag, c,c':Content, ee,ee':User, w,w':Wall |
		(invariants[n] and removeTag[n,n',n'',t,c,c',ee,ee',w,w']) implies
		(invariants[n'] and invariants[n''])
}

run removeTag for 3
check RemoveTagPreservesInvariant for 5

// --------- End: Operations --------
