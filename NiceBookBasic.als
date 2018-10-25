/*
 * Project 1: NiceBook
 * NiceBookBasic
 * 
 */

module NiceBook/NiceBookBasic

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
	tagger: one User,
	taggee: one User
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
	// A.7: user who can create content must belong to users
	(n.contents).Content in n.users
	// A.8: no two users can create the same content
	all u,u':n.users, c:Content | u->c in n.contents and u'->c in n.contents implies
	u = u'
	// Other invariants for comment and note
	commentInvariant[n]
	noteInvariant[n]
}

pred wallInvariant[n:SocialNetwork] {
	// B.6: Each user is given a unique wall
	all u,u':n.users | u'.wall = u.wall implies u' = u
	// A.10: content on the wall must in the social network contents relationship

	// Owner & friends & owner as tagee
	all u:n.users | all c:u.wall.items | 
	c in n.contents[u] or // owner
	c in n.friends[u].(n.contents) or // friends
	u in c.photoTags.taggee or // taggee
	u in c.noteTags.taggee // taggee
		
	// A.11: all walls has one user associated with it
	all w:Wall | one u:User | w = u.wall
}

fun get_noteTags[c:Content]: set Tag {
	c.noteTags
}

fun get_photoTags[c:Content]: set Tag {
	c.photoTags
}

fun get_tags[c:Content]: set Tag {
	get_noteTags[c] + get_photoTags[c]
}

pred tagInvariant[n:SocialNetwork] {
	// B.5 User can be tagged only by its friends
	all t: Tag, u, u': n.users | u = t.tagger and u' = t.taggee implies
	u -> u' in n.friends
	// noteTag and photoTag not overlap
	all c:Content | #(get_noteTags[c] & get_photoTags[c]) = 0
	// tags across contents not overlap
	all c,c':Content | c != c' implies #(get_tags[c] & get_tags[c']) = 0
	// every tag has a content associate with it
	all t:Tag | one c:Content | t in get_tags[c]
	// on a same photo or note, a user can only be tagged once
	all c:Content | all t,t': c.photoTags + c.noteTags | t != t' implies
	 t.taggee != t'.taggee
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
