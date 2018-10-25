module NiceBook/NiceBookPrivacy
open NiceBook/NiceBookBasic


fun viewable[u:User, n:SocialNetwork] : set Content {
	// visibility set to only/friends/friendsoffriends/everyone.
	// User can view their own content and content on their walls
	{r : (u.(n.contents) + u.wall.items)} + 
    // if Friends, u in friends[uploader]
	{r : Wall.items | all u' : u.(n.friends) | 
    u'.wall.wallPrivacy in Friends and u in ((n.contents).r).(n.friends)} +
    // if FriendsOfFriends, some f in friends[u] in friends[uploader] 
	{r : Wall.items | all u' : u.(n.friends) |
    u'.wall.wallPrivacy in FriendsOfFriends and 
	#(u.(n.friends) & ((n.contents).r).(n.friends)) > 0} + 
	// if Everyone implies viewable
	{r : Wall.items | all u' : u.(n.friends) |
    u'.wall.wallPrivacy in Everyone}
}

fun commentable[u:User, n:SocialNetwork] : set Content {
    // all contents that u owns
	{r : u.(n.contents)} + 
    // if Friends, u in friends[uploader]
	{r : Wall.items | ((n.contents).r).commentPrivacy in Friends and u in ((n.contents).r).(n.friends)} +
    // if FriendsOfFriends, some f in friends[u] in friends[uploader] 
	{r : Wall.items | ((n.contents).r).commentPrivacy in FriendsOfFriends and 
	#(u.(n.friends) & ((n.contents).r).(n.friends)) > 0} + 
	// if Everyone, then everyone can comment
	{r : Wall.items | ((n.contents).r).commentPrivacy in Everyone}
}

/*
In particular, we say that a privacy violation has occurred if a user 
is able to view a piece of content without adhering to the privacy level 
that is assigned to the content by its owner. Write an assertion
called NoPrivacyViolation to check that no such violation is possible.
*/
assert NoPrivacyViolation {
    all n : SocialNetwork, c : Wall.items, u : User |
    c in viewable[u,n] implies (
        // OnlyMe
        (c in (u.(n.contents) + u.wall.items)) or
        // Friends
        (c.viewPrivacy = Friends and u in ((n.contents).c).(n.friends)) or
        // FriendsOfFriends
        (c.viewPrivacy = FriendsOfFriends and 
	    #(u.(n.friends) & ((n.contents).c).(n.friends)) > 0) or
        // Everyone
        c.viewPrivacy = Everyone
    )
}

check NoPrivacyViolation for 10

