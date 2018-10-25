/*
 * Project 1: NiceBook
 * NiceBookBasic - Invariant and functions
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
pred usersInvariant[n:SocialNetwork] {
	// A.1: Users contain all the friends in the network
	User.(n.friends) + (n.friends).User in n.users
}

pred friendInvariant[n:SocialNetwork] {	
	// B.3: Friendship is a symmetric relation
	all u,u':n.users | u in n.friends[u'] implies u' in n.friends[u]
	// B.4: It is not possible for a user to be its own friend
	no u:n.users | u in n.friends[u] 
}

pred photoInvariant[n:SocialNetwork] {
	all photo:all_photos[n] | get_note_from_photo[photo] in User.(n.contents) 
}

pred commentInvariant[n:SocialNetwork] {
	// A.10: comment can not be attached to itself
	// A.11: No cycles in comments attachment 
	all c:all_comments[n] | c not in c.^attached
	// comment can only attach to content in the network
	all c:all_comments[n] | c.attached in User.(n.contents)
}

pred noteInvariant[n:SocialNetwork] {
	// A.6 two different note cannot include the same photo
	all note,note': all_notes[n] | 
	note != note' implies #(note.photos & note'.photos) = 0
	// A.13 Note can only contain photos created by the same user
	all note: all_notes[n], u: n.users | u->note in n.contents implies
	 (all p:note.photos | u->p in n.contents) 
}

pred contentInvariant[n:SocialNetwork] {
	// A.8: A user who can create content must belong to the set of User
	(n.contents).Content in n.users
	// A.9: No two users can post the same copy of a content
	all u,u':n.users, c:Content | u->c in n.contents and u'->c in n.contents implies
	u = u'
	// Other invariants for comment and note
	noteInvariant[n]
	photoInvariant[n]
	commentInvariant[n]
}

pred wallInvariant[n:SocialNetwork] {
	// B.6: Each user is given a unique wall
	all u,u':n.users | u'.wall = u.wall implies u' = u
	// A.12: content on the wall must in the social network contents relationship

	// A.16: A user cannot tag itself
	// Owner & friends & owner as tagee
	all u:n.users | all c:u.wall.items | 
	c in n.contents[u] or // owner
	c in n.friends[u].(n.contents) or // friends
	u in c.photoTags.taggee or // taggee
	u in c.noteTags.taggee // taggee
		
	// A.18: all walls has one user associated with it
	all w:Wall | one u:User | w = u.wall
}

pred tagInvariant[n:SocialNetwork] {
	// B.5 User can be tagged only by its friends
	all t: Tag, u, u': n.users | u = t.tagger and u' = t.taggee implies
	u -> u' in n.friends
	// A.14: No tags are shared among multiple notes/photos
	// noteTag and photoTag not overlap
	all c:Content | #(get_noteTags[c] & get_photoTags[c]) = 0
	// tags across contents not overlap
	all c,c':Content | c != c' implies #(get_tags[c] & get_tags[c']) = 0
	// A.16: Every tag has a content associate with it
	all t:Tag | one c:Content | t in get_tags[c]
	// A.15: A user can only be tagged once in the same note or photo
	all c:Content | all t,t': c.photoTags + c.noteTags | t != t' implies
	 t.taggee != t'.taggee
}

pred invariants[n:SocialNetwork] {
	usersInvariant[n]
	friendInvariant[n]
	contentInvariant[n]

	wallInvariant[n]
	tagInvariant[n]
}


run {
	all n:SocialNetwork | invariants[n]
} for 3 but exactly 1 SocialNetwork

fun get_note_from_photo[p:Photo] : set Note {
	{c:Note | p in c.photos}
}

fun all_notes[n:SocialNetwork]: set Note {
	User.(n.contents) & Note
}

fun all_photos[n:SocialNetwork]: set Photo {
	User.(n.contents) & Photo
}

fun all_comments[n:SocialNetwork]: set Comment {
	User.(n.contents) & Comment
}

fun all_comments[c:Content]: set Comment {
	{m:Comment | c in m.^attached}
}

fun get_related[c:Content] : set Content {
	c + c.photos + all_comments[c]
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
