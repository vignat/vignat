# Useful functions to perform common tasks.

# Overwrites the specified file as sudo with the specified contents.
# $1: The file
# $2: The contents
sudo_overwrite()
{
    echo $2 | sudo tee $1 > /dev/null
}

# Appends the specified contents to the specified file as sudo.
# $1: The file
# $2: The contents
sudo_append()
{
    echo $2 | sudo tee -a $1 > /dev/null
}
