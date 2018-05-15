#-*- coding: utf-8 -*-

import math

ANGLES=4

pic=[
"    **     ",
"    **     ",
"           ",
"   ***     ",
"    **     ",
"    **     ",
"    **     ",
"    **     ",
"    **     ",
"   ****    ",
"           "]

# https://en.wikipedia.org/wiki/Rotation_matrix
def rotate(pic, angle):
    WIDTH=len(pic[0])
    HEIGHT=len(pic)
    assert WIDTH==HEIGHT
    ofs=WIDTH/2

    out = [[" " for x in range(WIDTH)] for y in range(HEIGHT)]

    for x in range(-ofs,ofs):
        for y in range(-ofs,ofs):
            newX = int(round(math.cos(angle)*x - math.sin(angle)*y,3))+ofs
            newY = int(round(math.sin(angle)*x + math.cos(angle)*y,3))+ofs
            # clip at boundaries, hence min(..., HEIGHT-1)
            out[min(newX,HEIGHT-1)][min(newY,WIDTH-1)]=pic[x+ofs][y+ofs]
    return out

def rotate_and_print(angle):
    out=rotate(pic, angle)
    counts=[]
    for row in out:
        r="".join(row)
        print r, r.count("*")
        counts.append(r.count("*"))
    print counts, ","
    
WIDTH=len(pic[0])
HEIGHT=len(pic)
print "WIDTH=", WIDTH, "HEIGHT=", HEIGHT

for a in range(ANGLES):
    angle=a*(math.pi/ANGLES)
    print ("angle=(π/%d)*%d" % (ANGLES, a))
    rotate_and_print(angle)

