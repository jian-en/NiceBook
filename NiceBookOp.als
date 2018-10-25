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
	w'.items = w.items + c
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
	w'.items = w.items - c
}

// O.4: unpublish
pred unpublish[n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content] {
	// Precondition
	c in w.items
	// Operations
	unpublishWall[w,w',c]
	promotePublish[n,n',u,u',w,w',c]
}

run publish for 5 but exactly 2 SocialNetwork

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

// O.6: addTag
pred addTag[n,n':SocialNetwork, t:Tag, c,c':Content, er,ee:User] {
	// Precondition
	c in (n.users).(n.contents)
	c in Note + Photo
	er in n.users
	ee in n.users
	er in ee.(n.friends)
	// TODO: er can view c
	// Postcondition
	all u:((n.contents).c & n.users) | n'.contents = n.contents - u -> c + u -> c'
	// TODO: update comments attached to c
	// Add a tag to a photo or a note
	c'.noteTags = c.noteTags + t
	c'.photoTags = c.photoTags + t
	c'.viewPrivacy = c.viewPrivacy
	c'.photos = c.photos
	t.tagger = er
	t.taggee = ee
	// Automatically published onto ee's wall
}


run addTag for 3 but exactly 2 SocialNetwork

// O.7: removeTag
pred removeTag[n,n':SocialNetwork, t:Tag] {}

// --------- End: Operations --------
