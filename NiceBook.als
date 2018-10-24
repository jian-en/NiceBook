/*
 *NiceBook
 *
 */
module NiceBook

// ------ Start: Static Model -------
sig SocialNetwork {
	users: set User,
	contents: User -> some Content,
	friends: User -> set User
}

sig User {
	wall: one Wall,
	commentPrivacy: Privacy
}

abstract sig Content {
	viewPrivacy: Privacy
}

sig Note extends Content {
	photos: some Photo,
	noteTags: set Tag
}

sig Photo extends Content {
	photoTags: set Tag
}

sig Comment extends Content {
	attached: one Content
}

sig Tag {
	tagging: User -> one User
}

sig Wall { 
	// A.4 wall can be empty
	items: set Content,
	wallPrivacy: Privacy
}

abstract sig Privacy {}
one sig OnlyMe,Friends,FriendsOfFriends,Everyone extends Privacy {}

// ------ End: Static Model -------

pred friendInvariant[n:SocialNetwork] {
	// A.1: Users contain all the friends in the network
	User.(n.friends) + (n.friends).User in n.users	
	// B.3: Friendship is a symmetric relation
	all u,u':n.users | u in n.friends[u'] implies u' in n.friends[u]
	// B.4: It is not possible for a user to be its own friend
	no u:n.users | u in n.friends[u] 
}

pred commentInvariant[n:SocialNetwork] {
	// A.9: comment can not be attached to itself
	all c:Comment | c not in c.^attached
}

pred noteInvariant[n:SocialNetwork] {
	// A.6 two different note cannot include the same photo
	all note,note':Note | note != note' implies #(note.photos & note'.photos) = 0
	// Note can only contains photos to the same user
	all note:Note, u:User | u->note in n.contents implies
	 (all p:note.photos | u->p in n.contents)  
	
}

pred contentInvariant[n:SocialNetwork] {
	all c:Content | one n:SocialNetwork | c in User.(n.contents)
	// A.7: user who can create content must belong to users
	(n.contents).Content in n.users
	// A.8: no two users can create the same content
	all u,u':n.users, c:Content | u->c in n.contents and u'->c in n.contents implies
	u = u'
	commentInvariant[n]
	noteInvariant[n]
}

pred wallInvariant[n:SocialNetwork] {
	// B.6: Each user is given a unique wall
	all u,u':n.users | u'.wall = u.wall implies u' = u
	// A.10: content on the wall must in the social network contents relationship
	all u:n.users | all c:u.wall.items | u->c in n.contents
	// A.11: all walls has one user associated with it
	all w:Wall | one u:User | w = u.wall
}

pred tagInvariant[n:SocialNetwork] {
	// B.5 User can be tagged only by its friends
	all t: Tag, u, u': n.users | u in n.users and u' in n.users and 
	u->u' in t.tagging implies u->u' in n.friends
}


pred invariant[n:SocialNetwork] {
	friendInvariant[n]
	contentInvariant[n]
	wallInvariant[n]
	tagInvariant[n]
}

pred show[n:SocialNetwork] {
	invariant[n]
}

run show for 3 but exactly 1 SocialNetwork

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
pred remove[n,n':SocialNetwork, u:User, c:Content] {}

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
	// TODO: Maybe simpler way
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

// O.4: unpublish
pred unpublish[n,n':SocialNetwork, u:User, c:Content] {}

// O.5: addComment
pred addComment[n,n':SocialNetwork, u:User, c:Content] {
	// B.10: Own or visible content
}

// O.6: addTag
pred addTag[n,n':SocialNetwork, t:Tag, c:Content] {}

// O.7: removeTag
pred removeTag[n,n':SocialNetwork, t:Tag] {}

// --------- End: Operations --------

/*
fun viewable[u:User] : set Content {

}
assert NoPrivacyViolation {

}
*/

