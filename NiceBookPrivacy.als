module NiceBook/NiceBookPrivacy
open NiceBook/NiceBookBasic


fun viewable[u:User, n:SocialNetwork] : set Content {
	// visibility set to only/friends/friendsoffriends/everyone.
	// if only, c in contents[uploader]
	// if friends, u in friends[uploader]
	// if fof, some f in friends[u] in friends[uploader] 
	// c.viewPrivacy in everyone implies viewable
	{r : Content | r.viewPrivacy in OnlyMe and r in u.(n.contents)} + 
	{r : Content | r.viewPrivacy in Friends and u in ((n.contents).r).(n.friends)} +
	{r : Content | r.viewPrivacy in FriendsOfFriends and 
	#(u.(n.friends) & ((n.contents).r).(n.friends)) > 0} + 
	{r : Content | r.viewPrivacy in Everyone}
}
/*
assert NoPrivacyViolation {

}
*/
