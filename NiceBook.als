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
	wall: one Wall
}

abstract sig Content {
	contentPrivacy: Privacy,
	commentPrivacy: Privacy
}

sig Note extends Content {
	photos: some Photo,
	noteTags: some Tag
}

sig Photo extends Content {
	photoTags: some Tag
}

sig Comment extends Content {
	attached: one Content
}

sig Tag {
	reference: one User
}

sig Wall {
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

pred invariant [n:SocialNetwork] {
	friendInvariant[n]
}


pred show [n:SocialNetwork] {
	invariant[n]
	#n.users > 1
	#n.friends > 3
}

run show for 3 but 1 SocialNetwork

// -------- Start: Operations -------

pred upload[n,n':SocialNetwork, u:User, c:Content] {}
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

