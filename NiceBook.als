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

pred wallInvariant[n:SocialNetwork] {
	// B.6: Each user is given a unique wall
	all u,u':n.users | u'.wall = u.wall implies u' = u
}

pred tagInvariant[n:SocialNetwork] {
	// B.5 User can be tagged only by its friends
	all t: User.(n.contents).noteTags + User.(n.contents).photoTags, u, u': n.users | u->u' in t.tagging implies u->u' in n.friends
}


pred invariant[n:SocialNetwork] {
	friendInvariant[n]
	wallInvariant[n]
	tagInvariant[n]
}

pred show[n:SocialNetwork] {
	invariant[n]
	#n.users > 1
	#n.friends > 2
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





pred remove[n,n':SocialNetwork, u:User, c:Content] {}
pred publish[n,n':SocialNetwork, u:User, c:Content] {}
pred unpublish[n,n':SocialNetwork, u:User, c:Content] {}
pred addComment[n,n':SocialNetwork, u:User, c:Content] {}
pred addTag[n,n':SocialNetwork,t:Tag, c:Content] {}
pred removeTag[n,n':SocialNetwork,t:Tag] {}

// --------- End: Operations --------

/*
fun viewable[u:User] : set Content {

}
assert NoPrivacyViolation {

}
*/

