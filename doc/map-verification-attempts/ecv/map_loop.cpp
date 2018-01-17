/*-------------------------------------------------------*/
/* File:    /home/necto/proj/vnds/ecv/map_loop.cpp       */
/* Author:  necto                                        */
/* Created: 09:36:28 on Tuesday September 22nd 2015 UTC  */
/*-------------------------------------------------------*/

#include "ecv.h"
#include "map.h"


int loop (int k)
{
    //single "%" result ranges from -CAPACITY to CAPACITY.
    return (k%CAPACITY + CAPACITY)%CAPACITY;//ranges from 0 to CAPACITY.
}
