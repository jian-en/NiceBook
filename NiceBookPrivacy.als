module NiceBook/NiceBookPrivacy
open NiceBook/NiceBookBasic


fun validFriends[u:User, n:SocialNetwork]: set User {
	{u':u.(n.friends) | u'.wall.wallPrivacy in (Friends + FriendsOfFriends + Everyone)}
}

fun validFoF[u:User, n:SocialNetwork]: set User {
	{u':u.(n.friends).(n.friends) | u'.wall.wallPrivacy in (FriendsOfFriends + Everyone)}
}

fun validUser[u:User, n:SocialNetwork]: set User {
	{u':n.users | u'.wall.wallPrivacy = Everyone}
}

fun viewable[u:User, n:SocialNetwork] : set Content {
	n.contents[u] +  // 1. created by myself
	u.wall.items +  // 2. on the wall
	
	validFriends[u,n].wall.items +  // 3. on valid friends' walls
	validFoF[u,n].wall.items +  // 4. on valid fofriends' walls
	validUser[u,n].wall.items // 5. on valid users' walls
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

assert NoPrivacyViolation {
    all n : SocialNetwork | all u : n.users, c : (n.users).(n.contents) |
    	c in viewable[u,n] and invariants[n] implies (
        // OnlyMe
        (c in n.contents[u] + u.wall.items) or
        // Friends
        (c.viewPrivacy = Friends and (n.contents).c in u.(n.friends)) or
        // FriendsOfFriends
        (c.viewPrivacy = FriendsOfFriends and 
	    (n.contents).c in u.(n.friends).(n.friends) - u + u.(n.friends)) or
        // Everyone
        (c.viewPrivacy = Everyone)
    )
}

check NoPrivacyViolation for 5

