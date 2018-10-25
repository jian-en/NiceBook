module NiceBook/NiceBookPrivacy
open NiceBook/NiceBookBasic


fun viewable[u:User, c:Content, n:SocialNetwork] : set Content {
	// visibility set to only/friends/friendsoffriends/everyone.
	// if only, c in contents[uploader]
	// if friends, u in friends[uploader]
	// if fof, some f in friends[u] in friends[uploader] 
	// c.viewPrivacy in everyone implies viewable
	{r : Content | c.viewPrivacy in OnlyMe and c in u.(n.contents) implies r = c} + 
	{r : Content | c.viewPrivacy in Friends and u in ((n.contents).c).(n.friends) implies r = c} +
	{r : Content | c.viewPrivacy in FriendsOfFriends and 
	#(u.(n.friends) & ((n.contents).c).(n.friends)) > 0 implies r = c} + 
	{r : Content | c.viewPrivacy in Everyone implies r = c}
}
/*
assert NoPrivacyViolation {

}
*/
