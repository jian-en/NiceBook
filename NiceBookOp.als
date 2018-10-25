/*
 *NiceBook
 *
 */
module NiceBook/NiceBookOp
open NiceBook/NiceBookBasic
open NiceBook/NiceBookPrivacy


// -------- Start: Operations -------
// A.2: The social network has a fixed set of users/friendships
pred networkOp[n,n':SocialNetwork] {
	n'.users = n.users
	n'.friends = n.friends
}

// O.1: upload
pred upload[n,n':SocialNetwork, u:User, c:Content] {
	networkOp[n,n']	
	// Precondition
	c not in User.(n.contents) and u in n.users
	no c.noteTags and no c.photoTags
	// Postcondition
	n'.contents = n.contents + u->c
}

assert UploadPreserveInvariant {
	all n, n': SocialNetwork, u:User, c:Content |
		invariant[n] and upload[n,n',u,c] implies
		invariant[n']
}

check UploadPreserveInvariant for 2 but exactly 2 SocialNetwork

// O.2: remove
pred remove[n,n':SocialNetwork, u:User, c:Content] {
	networkOp[n,n']
	// Precondition
	c in User.(n.contents) and u in n.users
	u->c in n.contents 
	// Postcondition
	n'.contents = n.contents - u->c	
}
assert RemovePreserveInvariant {
	all n, n': SocialNetwork, u:User, c:Content |
	invariant[n] and upload[n,n',u,c] implies
	invariant[n']
}
check RemovePreserveInvariant for 2 but exactly 2 SocialNetwork
fact {
	all n:SocialNetwork | invariant[n]
}
run remove for 3

// Local states in O.3
pred publishWall[w,w':Wall, c:Content] {
	w'.wallPrivacy = w.wallPrivacy
	// Publish to the wall
	w'.items = w.items + c
}

// Global states in O.3
pred promotePublish[n,n':SocialNetwork, u,u':User, w,w':Wall] {
	// Precodition
	u in n.users
	u.wall = w
	// Postcondition
	u'.wall = w'
	n'.users = n.users - u + u'
	all u1 : u.(n.friends) | n'.friends = n.friends - u -> u1 + u' -> u1
	all u2 : (n.friends).u | n'.friends = n.friends - u2 -> u + u2 -> u
}

// O.3: publish
pred publish[n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content] {
	// If c is a new one
	n'.contents = n.contents + u -> c
	// B.8: Notes and photos from the user or its friends can be published
	c in u.(n.contents) + u.(n.friends).(n.contents)
	c in Note + Photo
	// Operations
	publishWall[w,w',c]
	promotePublish[n,n',u,u',w,w']
}

//fact {
//	all n:SocialNetwork | invariant[n]
//}
//
//run publish for 3

assert PublishPreserveInvariant {
	all n,n':SocialNetwork, u,u':User, w,w':Wall, c:Content |
		invariant[n] and publish[n,n',u,u',w,w',c] implies
		invariant[n']
}

check PublishPreserveInvariant for 2 but exactly 2 SocialNetwork

// O.4: unpublish
pred unpublish[n,n':SocialNetwork, u:User, c:Content] {}

// O.5: addComment
pred addComment[n,n':SocialNetwork, u:User, c:Comment, x:Content] {
	// B.10: Own or visible content
	x in viewable[u,x,n]
	networkOp[n,n']
	c not in User.(n.contents)
	// Add comment
	n'.contents = n.contents + u->c
	c.attached = x
}

assert AddPreservesInvariant {
	all n,n':SocialNetwork, u:User, c:Comment, x:Content |
		invariant[n] and addComment[n,n',u,c,x] implies
		invariant[n']	
}

check AddPreservesInvariant for 5

run addComment for 10

// O.6: addTag
pred addTag[n,n':SocialNetwork, t:Tag, c:Content] {}

// O.7: removeTag
pred removeTag[n,n':SocialNetwork, t:Tag] {}

// --------- End: Operations --------
