#python module for performing various crypto related functions.

#version 19, fixed route tramp spiral bug that occured if height > width
#version 18, added 6x6 bazeries
#version 14, in monome-dinome allow user to specify second substitution
#version 13, allow j's in plaintext of Bazeries, convert j's to i's in encode routine. 
#version 12, added 6x6 nihilist substitution
#version 11, added 6x6 checkerboard
#verson 10 added simple substitution encode/decode
#version 9, change nihilist tramp to use inverse key instead of columnar type key, aligns with ACA&you
#version 8, 10x10 Grandpre, use order 0-9, fror route_encrypt_decrypt, remove print_matrix and substitute 
# include_digits. For 6x6 keysquare, if length of key is already 36, leave it as is, no digits to add.

#for acaencodedecode, version 6, fix ragbaby hyphen, apostrophe problem

#for acaencode-decode, version 4

# 2/14/2011 redid homophonic decode routine to allow for formats other than code pairs separated by blanks
# 2/14/2011 redid pollux, encode-decode routines to make compatable with appengine, and add error message
# 2/14/2011 added error message to fractionated morse amd morbit decode routines
# 2/14/2011 changed columnar hat routine to remove blanks from alphabetic keys
# 2/13/2011 changed homophonic encoide to output pairs of digits without spaces
# 2/13/2011 added numbered-key encode,decode
# Special rewrite of Fract Morse encode for appengine, 2-6-2011
# added periodic_gromark_primer routine so can return a primer for ACA composers to include, 2-6-2011
#change trisquare cipher output not to add space after each 3 letter group. will add later. 2-7-11
#change ragbaby routine to eliminate 'trans' call. 2-7-11
#change ragbaby decoding routine to send J to I and X to W, 2-10-11
# Special rewrite of Morbit encode for appengine, 2-11-11


# $Id: crypto.py,v 2.15 2007/09/17 23:35:58 williammason Exp williammason $
# $Log: crypto.py,v $
# Revision 2.15  2007/09/17 23:35:58  williammason
# Fixed variant autokey bug in vig family ID test routine.
#
# Revision 2.14  2007/09/17 23:04:27  williammason
# added porta autokey to vig family encode/decode and analysis routines
#
# Revision 2.13  2006/11/18 03:33:35  williammason
# fixed another bug in seriated playfair encoding routine.
#
# Revision 2.12  2006/11/16 19:26:28  williammason
# Fixed errors in Morse code punctuation symbols and added @ ' " symbols.
# Added Phillips-C and Phillips-RC encoding/decoding routines.
#
# Revision 2.11  2006/06/22 18:51:52  williammason
# Added REV_DIAGONAL (reverse diagonal -- from top downward) route to route transposition routine.
#
# Revision 2.10  2006/06/21 18:24:45  williammason
# added switch to route transposition encrypt/decrypt routine to allow reversing the input string, and reverseing the output string.
# Without the reverse there are 281 different routes, with it, there are 344 different routes. Need reverse output_string switch to
# decrypt a cipher that was encrypted by reversing the input (plaintext) string.
#
# Revision 2.9  2006/06/20 19:13:08  bill
# Added encrypt, decrypt routine for route transposition.
#
# Revision 2.8  2005/03/11 22:15:51  bill
# Changed get_hat_offset routine to allow numerical keys longer than 26 in
# columnar, nihilist, and amsco transposition, and to allow the numerical
# keys to be relativev to 0 or to 1. Removed integer_key_convert routine.
#
# Revision 2.7  2004/05/05 19:45:35  bill
# Added 6x6 option to trisquare encode and decode routines.
#
# Revision 2.6  2004/04/04 17:09:48  bill
# fixed ROD routine to handle case with zero repeats.
# Added running key encode and decode routines.
#
# Revision 2.5  2004/02/23 12:54:58  bill
# Fixed bug in seriated_playfair_encode routine.
#
# Revision 2.4  2003/11/24 19:07:20  bill
# Added progressive key encode and decode routines.
#
# Revision 2.3  2003/11/15 19:28:29  bill
# Added tridigital encoding routine.
#
# Revision 2.2  2003/11/15 15:43:26  bill
# Added checking for correct key length to morbit encode and decode.
#
# Revision 2.1  2003/10/13 17:37:21  bill
# Added new keysquare routes, 11 is alternate up, then down,
# and 12 is clockwise spiral starting at lower left corner
#
# Revision 1.28  2003/09/17 16:21:27  bill
# Fixed ragbaby encode to send plaintext j to i and x to w.
# Added monome-dinome encode, decode routines.
# Added headline puzzle encode-decode routines.
#
# Revision 1.27  2003/09/16 18:07:28  bill
# Added swagman encode and decode routines.
#
# Revision 1.26  2003/09/15 18:23:54  bill
# Added Grandpre encode, decode routines.
# Changed import math to from math import sqrt.
#
# Revision 1.25  2003/09/14 18:23:56  bill
# Added Grille encode and decode routines.
# Added Baconian encode and decode routines.
#
# Revision 1.24  2003/09/13 19:11:19  bill
# Added Nihilist substitution encode and decode.
# Added CM Bifid encode and decode.
#
# Revision 1.23  2003/09/13 16:08:03  bill
# Added morbit encode, decode routines.
# Added pollux encode, decode routines.
# Moved morse dictionaries to global variables.
#
# Revision 1.22  2003/09/12 17:04:13  bill
# Added checkerboard encode, decode routines.
# Added Bazeries encode, decode routines.
#
# Revision 1.21  2003/09/11 16:34:48  bill
# Added nihilist transposition encode, decode routines.
# Added option for numerical keys in columnar routines.
#
# Revision 1.20  2003/09/09 18:33:47  bill
# Added Amsco encode, decode, and display routines.
#
# Revision 1.19  2003/09/08 15:49:33  bill
# Added Portax routines.
#
# Revision 1.18  2003/09/07 14:38:56  bill
# Added Nicodemus encode and decode routines.
#
# Revision 1.17  2003/09/06 20:33:39  bill
# Added encode and decode routines for ciphers in the Vigenere family
# same ones as convered by AAHJU's vig tests.
#
# Revision 1.16  2003/09/03 19:34:38  bill
# Added redefence encode and decode routines.
#
# Revision 1.15  2003/09/02 19:37:20  bill
# added ragbaby encode and decode routines.
#
# Revision 1.14  2003/09/01 19:06:12  bill
# Fixed bug in 6x6 keysquare route. Added more 6x6 routes.
# Added Cadenus endcode and decode routines.
# Added Myszkowski encode and decode routines
#
# Revision 1.13  2003/08/28 19:13:40  bill
# Simplified fractionated_morse_decode.
# Added 6x6 switches to seriated playfair encode and decode and
# playfair encode and decode.
#
# Revision 1.12  2003/08/25 19:52:21  bill
# Added fractionated morse encode and decode.
#
# Revision 1.11  2003/08/24 15:46:17  bill
# Added phillips_encode and phillips_decode.
#
# Revision 1.10  2003/08/22 15:51:52  bill
# Put 6x6 switches into convert_string, convert_to_string, get_key_array,
# get_keysquare, find_keysquare_coordinates, two_square_encode,
# two_square_decode, four_square encode and decode, bifid encode and decode.
#
# Revision 1.9  2003/08/21 18:10:45  bill
# Added _6x6_ versions of convert_string, convert_to_string, get_key_array,
# get_keysquare, find_keysquare_coordinates, bifid_encode, bifid_decode.
#
# Revision 1.8  2003/08/21 14:05:48  bill
# Added digrafid endcode and decode routines.
#
# Revision 1.7  2003/08/20 18:57:26  bill
# Changed convert_string, convert_to_string, and get_key_array routines
# to handle 27 letter alphabets that include the # character.
# Added trifid encode and decode routines.
#
# Revision 1.6  2003/08/19 18:55:23  bill
# Added new keysquare route. Added bifid encode and bifid decode routines.
#
# Revision 1.5  2003/08/18 15:50:30  bill
# Added seriated Playfair encode and decode routines.
# changed playfair encode and decode to call seriated versions with
# a period of one
#
# Revision 1.4  2003/08/17 19:22:49  bill
# Added playfair routines: playfair_encode and playfair_decode
#
# Revision 1.3  2003/08/17 16:09:51  bill
# Made get_dic() function shorter
#
import string
from math import sqrt
from random import randrange

def convert_6x6_string(s):
    """
    convert letters and digits in string s to a list
    of code integers relative to A=0,Z=25,'1' = 26,..'0'=35 etc
    """
    s1 = s.upper()
    list = []
    for c in s1:
        i = ord(c)
        if i >= ord('A') and i <= ord('Z'):
            x = i - ord('A')
            list.append(x)
        elif i == ord('0'):
            list.append(35)
        elif i> ord('0') and i <= ord('9'):
            list.append( i-ord('1')+26 )
    return list

def convert_string(s,noJ=0,yes_sharp=0,use6x6=0):
    """
    convert letters in string s to a list
    of code integers relative to A=0,
    if yes_sharp is non-zero, replace \# with integer 26
    """
    if use6x6: return convert_6x6_string(s)
    s1 = string.upper(s)
    list = []
    for c in s1:
        if noJ and c == 'J':
            c = 'I'
        i = ord(c)
        if i >= ord('A') and i <= ord('Z'):
            x = i - ord('A')
            list.append(x)
        elif yes_sharp and i == ord('#'):
            list.append(26)
    return list

def convert_numb_string(number):
    """
    convert number string to list of digits
    """
    list = []
    for n in number:
        d = ord(n)
        if d <= ord('9') and d >= ord('0'):
            list.append( d - ord('0'))
    return list

def convert_to_6x6_string(code):
    """
    convert list of code integers into string of lowercase letters,
    plus digits
    """
    alpha1 = "abcdefghijklmnopqrstuvwxyz1234567890"
    text = ''
    for n in code:
        text += alpha1[n]
    return text

def convert_to_string(code,use6x6=0):
    """
    convert list of code integers into string of lowercase letters,
    replace 26 with \#
    """
    if use6x6: return convert_to_6x6_string(code)
    text = [chr(n+ord('a')) for n in code]
    text = ''.join(text)
    text = text.replace('{','#')
    return text

def get_6x6_key_array(key):
    """
    key is a string, usually a word, to extend to a complete
    array of coded integers, with the correct 'digits' inserted after the
    'letters'. We assume that the key string itself does not include digits.
    """
    key_code = convert_6x6_string(key)
    if len(key_code) == 36: # already done!
        return key_code
    already_used = [0]*26
    key_array = []
    for i in key_code:
        if already_used[i] == 0:
            key_array.append(i)
            already_used[i] = 1
            if i < 10 :
                key_array.append(i+26)
    for i in range(26):
        if already_used[i] == 0:
            key_array.append(i)
            if i < 10:
                key_array.append(i+26)
    return key_array

def get_6x6_keysquare(key,route=0):
    """
    given key word(s) string and route number, return
    keysquare list of coded integers
    """
    array = get_6x6_key_array(key)
    routes = [None]*13
    #horizontal
    routes[0] = range(36)
    #left-right
    routes[1] = [ 0,1,2,3,4,5,11,10,9,8,7,6,12,13,14,15,16,17,23,22,21,20,19,18,24,\
             25,26,27,28,29,35,34,33,32,31,30]
    #spiral
    routes[2] = [0,1,2,3,4,5,19,20,21,22,23,6,18,31,32,33,24,7,17,30,35,34,25,8,16,\
             29,28,27,26,9,15,14,13,12,11,10]
    # 3 vertical
    routes[3] = [0,6,12,18,24,30,1,7,13,19,25,31,2,8,14,20,26,32,3,9,15,21,27,33,4,\
             10,16,22,28,34,5,11,17,23,29,35]
    # 4 down up
    routes[4] = [0,11,12,23,24,35,1,10,13,22,25,34,2,9,14,21,26,33,3,8,15,20,27,32,\
                 4,7,16,19,28,31,5,6,17,18,29,30]
    #  5 counter clockwise spiral
    routes[5] = [0,19,18,17,16,15,1,20,31,30,29,14,2,21,32,35,28,13,3,22,33,34,27,12,\
             4,23,24,25,26,11,5,6,7,8,9,10]
    # 6 vert up
    routes[6] = [5,11,17,23,29,35,4,10,16,22,28,34,3,9,15,21,27,33,2,8,14,20,26,32,1,\
                  7,13,19,25,31,0,6,12,18,24,30]
    # 7 diagonal up
    routes[7] = [0,2,5,9,14,20,1,4,8,13,19,25,3,7,12,18,24,29,6,11,17,23,28,32,10,16,\
                   22,27,31,34,15,21,26,30,33,35]
    # 8 diagonal alternating up and down
    routes[8] = [0,2,3,9,10,20,1,4,8,11,19,21,5,7,12,18,22,29,6,13,17,23,28,30,14,16,\
                  24,27,31,34,15,25,26,32,33,35]
    # 9 diagonal down, start at right corner
    routes[9] = [15,10,6,3,1,0,21,16,11,7,4,2,26,22,17,12,8,5,30,27,23,18,13,9,33,31,28,\
                    24,19,14,35,34,32,29,25,20]
    # 10 clockwise spiral starting at bottom right
    routes[10] = [10,11,12,13,14,15,9,26,27,28,29,16,8,25,34,35,30,17,7,24,33,32,31,18,\
                    6,23,22,21,20,19,5,4,3,2,1,0]
    # 11 vertical up-down
    routes[11] = [5,6,17,18,29,30,4,7,16,19,28,31,3,8,15,20,27,32,2,9,14,21,26,33,1,10,13,\
                    22,25,34,0,11,12,23,24,35]
    # 12 spiral from lower left
    routes[12] = [5,6,7,8,9,10,4,23,24,25,26,11,3,22,33,34,27,12,2,21,32,35,28,13,1,20,31,\
                    30,29,14,0,19,18,17,16,15]
    
    newarray = [None]*36
    for i in range(36):
        newarray[i] = array[ routes[route][i] ]
    square = [None]*6
    for i in range(6):
        square[i] = newarray[ 6*i : 6*(i+1) ]
    return square


def get_key_array(key,skip,yes_sharp = 0,use6x6=0):
    """
    key is a string, usually a word, to extend to a complete
    array of coded integers, omitting the letters in the string 'skip' (usually 'j'
    or None )
    If yes_sharp is non-zero use 27 letter alphabet.
    """
    if use6x6 : return get_6x6_key_array(key)
    key_code = convert_string(key,noJ=0,yes_sharp=yes_sharp)
    skip_code = convert_string(skip)
    # convert any letters in key that are in skip
    #to their predecessors (probably not in skip
    for i in range(len(key_code)):
        if key_code[i] in skip_code:
            key_code[i] -= 1
    if yes_sharp: numb_letters = 27
    else: numb_letters = 26
    already_used = [0]*numb_letters
    for i in skip_code:
        already_used[i] = 1
    key_array = []
    for i in key_code:
        if already_used[i] == 0:
            key_array.append(i)
            already_used[i] = 1
    for i in range(numb_letters):
        if already_used[i] == 0:
            key_array.append(i)
    return key_array

def output_code_groups(ctext,bl=5,nl=55):
    """
    input string ctext, output ctext converted to upper case
    plus a blank every bl letters and a new line every nl letters
    """
    utext = string.upper(ctext)
    newtext = ""
    count = 0
    for i in range(len(ctext)):
        newtext += utext[i]
        count += 1
        if (count % bl) == 0: newtext += ' '
        if (count % nl) == 0 : newtext += '\n'
    return newtext

def get_keysquare(key,route=0,use6x6=0):
    """
    given key word(s) string and route number, return
    keysquare list of coded digits.
    """
    if use6x6: return get_6x6_keysquare(key,route=route)
    array = get_key_array(key,'j')
    routes = [None]*13
    #horizontal
    routes[0] = range(25)
    #left-right
    routes[1] = [ 0,1,2,3,4,9,8,7,6,5,10,11,12,13,14,19,18,17,16,15,20,21,22,23,24]
    #spiral
    routes[2] = [0,1,2,3,4,15,16,17,18,5,14,23,24,19,6,13,22,21,20,7,12,11,10,9,8]
    # 3 vertical
    routes[3] = [0,5,10,15,20,1,6,11,16,21,2,7,12,17,22,3,8,13,18,23,4,9,14,19,24]
    # 4 down up
    routes[4] = [0,9,10,19,20,1,8,11,18,21,2,7,12,17,22,3,6,13,16,23,4,5,14,15,24]
    #  5 counter clockwise spiral
    routes[5] = [0,15,14,13,12,1,16,23,22,11,2,17,24,21,10,3,18,19,20,9,4,5,6,7,8]
    # 6 vert up
    routes[6] = [4,9,14,19,24,3,8,13,18,23,2,7,12,17,22,1,6,11,16,21,0,5,10,15,20]
    # 7 diagonal up
    routes[7] = [0,2,5,9,14,1,4,8,13,18,3,7,12,17,21,6,11,16,20,23,10,15,19,22,24]
    # 8 diagonal alternating up and down
    routes[8] = [0,2,3,9,10,1,4,8,11,18,5,7,12,17,19,6,13,16,20,23,14,15,21,22,24]
    # 9 diagonal down, start at right corner
    routes[9] = [10,6,3,1,0,15,11,7,4,2,19,16,12,8,5,22,20,17,13,9, 24,23,21,18,14]
    # 10 clockwise spiral starting at bottom right
    routes[10] = [8,9,10,11,12,7,20,21,22,13,6,19,24,23,14,5,18,17,16,15,4,3,2,1,0]
    # 11 vertical alternate up, then down
    routes[11] = [4,5,14,15,24,3,6,13,16,23,2,7,12,17,22,1,8,11,18,21,0,9,10,19,20]
    # 12 clockwise spiral starting at lower left corner.
    routes[12] = [4,5,6,7,8,3,18,19,20,9,2,17,24,21,10,1,16,23,22,11,0,15,14,13,12]

    newarray = [None]*25
    for i in range(25):
        newarray[i] = array[ routes[route][i] ]
    square = [None]*5
    for i in range(5):
        square[i] = newarray[ 5*i : 5*(i+1) ]
    return square

def find_keysquare_coordinates(c, keysquare,use6x6=0):
    """
    given code digit c and key square, return the
    row and column coordinates of c in the square
    """
    if use6x6: length = 6
    else : length = 5
    for row in range(length):
        for col in range(length):
            if c == keysquare[row][col]:
                return [ row,col]
    return [-1,-1] # c not in square!

def get_quagmire_array(plain_key,code_key,indicator_key,plain_align_let):
    """
    return quagmire array as lines of code digits with the last line as the
    plaintext array. Input strings are:
    plain key, code key, indicator key, and plain letter to align
    indicator key beneath. For quagmire IV, the keys are different.
    In Quagmire III, plain and code keys are the same. In Quagmire II,
    plain key is just 'A'. In Quagmire I, code key is just 'A'
    """
    period = len(indicator_key);
    quag_array = [None]*(period+1)
    plain_array = get_key_array(plain_key,'')
    coded_array = get_key_array(code_key,'')
    ps = convert_string(plain_align_let)[0]
    cl = convert_string(indicator_key)
    n = plain_array.index(ps)
    for index in range(period):
        quag_array[index] = [0]*26
        cs = cl[index]
        m = coded_array.index(cs)
        for i in range(26):
            quag_array[index][i] = coded_array[ (26+i+m-n)%26]
    quag_array[period] = plain_array
    return quag_array

def quagmire_encode(plaintext,plain_key,code_key,indicator_key,plain_align_let):
    """
    encrypt the string plaintext as a Quagmire with given keys,
    output uppercase codetext
    """
    plain = convert_string(plaintext)
    period = len(indicator_key)
    qa = get_quagmire_array(plain_key,code_key,indicator_key,plain_align_let)
    code = [0]*len(plain)
    count = 0
    index = 0
    for pl in plain:
        n = qa[period].index(pl)
        code[count] = qa[index][n]
        count += 1
        index += 1
        if index == period: index = 0
    codetext = convert_to_string(code)
    return string.upper(codetext)

def quagmire_decode(codetext,plain_key,code_key,indicator_key,plain_align_let):
    """
    decrypt the string codetext as a Quagmire with given keys,
    output the lowercase plaintext
    """
    code = convert_string(codetext)
    period = len(indicator_key)
    qa = get_quagmire_array(plain_key,code_key,indicator_key,plain_align_let)
    plain = [0]*len(code)
    count = 0
    index = 0
    for ct in code:
        n = qa[index].index(ct)
        plain[count] = qa[period][n]
        count += 1
        index += 1
        if index == period: index = 0
    plaintext = convert_to_string(plain)
    return plaintext

#columnar, cadenus, myszkowski, redefence transposition routines
def get_hat_offset(hat):
    """
    Input key word(s) string or string of integers separated by blanks
    and return list of numerical offsets for columnar transposition.
    If integer string, it can be relative to 0 or to 1
    """
    if hat.find('1') == -1:
        alphabet = "abcdefghijklmnopqrstuvwxyz"
        lhat = hat.lower()
        lhat = lhat.replace(' ','')
        offset = []
        for c in alphabet:
            for i in range(len(lhat)):
                if c == lhat[i]:
                    offset.append(i)
    else:
        key = hat.split()
        if key.count('0') == 0:
            n = 1
        else:
            n = 0
        nkey = [int(s)-n for s in key]
        #print nkey
        offset = []
        for i in range(len(nkey)):
            for k in range(len(nkey)):
                if i == nkey[k]:
                    offset.append(k)
    return offset

def offset_to_key(offset):
    """
    given offset list for columnar transposition, return
    the numerical key as a list. (inverse of offset)
    """
    key = [None]*len(offset)
    for i in range(len(offset)):
        x = offset.index(i)
        key[i] = x
    return key

def display_transposition_block(plaintext,key_len):
    """
    input string plaintext, and integer key_len,
    return the corresponding transposition block
    """
    plain = convert_string(plaintext)
    plain = convert_to_string(plain)
    ct = 0
    display = ''
    for c in plain:
        display += c+' '
        ct += 1
        if ct == key_len:
            display += '\n'
            ct = 0
    display += '\n'
    return display
    
def columnar_encode(plaintext,hat):
    """
    Encrypt the string plaintext with the hat string as columnar
    transposition key. Return uppercase ciphertext string.
    """
    plain = convert_string(plaintext)
    offset = get_hat_offset(hat)
    kl = len(offset)
    code = []
    for n in offset:
        for pos in range(n,len(plain),kl):
            code.append(plain[pos])
    codetext = convert_to_string(code)
    display = display_transposition_block(plaintext,kl)
    return [string.upper(codetext),display]

def columnar_decode(codetext,hat):
    """
    decrypt the string codetext with the string hat as columnar
    transposition key. return lowercase plaintext string
    """
    code = convert_string(codetext)
    offset = get_hat_offset(hat)
    kl = len(offset)
    plain = [None]*len(code)
    index = 0
    for n in offset:
        for pos in range(n,len(code),kl):
            plain[pos] = code[index]
            index += 1
    plaintext = convert_to_string(plain)
    display = display_transposition_block(plaintext,kl)    
    return [plaintext,display]

def nihilist_transposition_encode(plaintext,key,by_rows = 0):
    """
    input strings plaintext and key. key can be
    alphabetic or numbers separated by blanks.
    if by_rows is nonzero, take off by rows.
    Output nihilist tramp codetext string.
    """
    plain = convert_string(plaintext)
    #offset = get_hat_offset(key)
    #use inverse of columnar offset for compatibility with ACA&You
    coffset = get_hat_offset(key)
    key_len = len(coffset)
    offset = [None]*key_len
    for i in range(key_len):
        offset[coffset[i]] = i
    if key_len*key_len != len(plain):
        print "Plaintext does not fit into a square!"
        return "ERROR"
    code = []
    c1 = 1
    c2 = key_len
    if by_rows :
        c2=1
        c1 = key_len
    for col in range(key_len):
        for row in range(key_len):
            code.append( plain[ offset[col]*c1+offset[row]*c2 ] )
    codetext = convert_to_string(code)
    display = display_transposition_block(plaintext,key_len) 
    if by_rows == 0:
        temp = []
        for col in range(key_len):
            for row in range(key_len):
                temp.append( plain[ offset[col]*key_len+offset[row] ])
        display2 = convert_to_string(temp)
        display2 = display_transposition_block(display2,key_len).upper()
    else:
        display2 = display_transposition_block(codetext,key_len).upper()            
    return [codetext,display,display2]

def nihilist_transposition_decode(codetext,key,by_rows = 0):
    """
    input strings codetext and key. key can be
    alphabetic or numbers separated by blanks.
    if by_rows is nonzero, take off by rows.
    Output nihilist tramp plaintext string.
    """
    code = convert_string(codetext)
    #offset = get_hat_offset(key)
    #use inverse of columnar offset for compatibility with ACA&You
    coffset = get_hat_offset(key)
    key_len = len(coffset)
    offset = [None]*key_len
    for i in range(key_len):
        offset[coffset[i]] = i
    if key_len*key_len != len(code):
        print "codetext does not fit into a square!"
        return "ERROR"
    c1 = 1
    c2 = key_len
    if by_rows :
        c2=1
        c1 = key_len
    plain = [None]*len(code)
    pos = 0
    for col in range(key_len):
        for row in range(key_len):
            plain[ offset[col]*c1+offset[row]*c2 ]  = code[pos]
            pos += 1
    plaintext = convert_to_string(plain)
    display = display_transposition_block(plaintext,key_len)
    if by_rows == 0:
        temp = []
        for col in range(key_len):
            for row in range(key_len):
                temp.append( plain[ offset[col]*key_len+offset[row] ])
        display2 = convert_to_string(temp)
        display2 = display_transposition_block(display2,key_len).upper()
    else:
        display2 = display_transposition_block(codetext,key_len).upper()            
    return [plaintext,display,display2]

def cadenus_encode(plaintext,hat):
    """
    Encrypt the string plaintext with the hat string as cadenus
    transposition. Return uppercase ciphertext string.
    """
    plain = convert_string(plaintext)
    offset = get_hat_offset(hat)
    kl = len(offset)
    if len(plain) != 25 * kl :
        print "Text not multiple of 25!"
        return "ERROR"
    key = convert_string(hat)
    # map "W" to "V", etc.
    for i in range(len(key)):
        if key[i] >= ord('w')-ord('a') : key[i] -= 1
    code = []
    for row in range(25):
        for n in offset:
            shift = (25-key[n]+row)%25
            pos = n + shift*kl
            code.append(plain[pos])
    codetext = convert_to_string(code)
    return codetext.upper()

def cadenus_decode(codetext,hat):
    """
    decrypt the string codetext with the hat string as cadenus
    transposition. Return plaintext string.
    """
    code = convert_string(codetext)
    offset = get_hat_offset(hat)
    kl = len(offset)
    if len(code) != 25 * kl :
        print "Text not multiple of 25!"
        return "ERROR"
    key = convert_string(hat)
    # map "W" to "V", etc.
    for i in range(len(key)):
        if key[i] >= ord('w')-ord('a') : key[i] -= 1
    plain = [None]*len(code)
    index = 0
    for row in range(25):
        for n in offset:
            shift = (25-key[n]+row)%25
            pos = n + shift*kl
            plain[pos] = code[index]
            index += 1
    plaintext = convert_to_string(plain)
    return plaintext

def myszkowski_encode(plaintext,key):
    """
    encode string plaintext with string key as myszkowski
    transposition. Output unformatted codetext string.
    """
    plain = convert_string(plaintext)
    key_code = convert_string(key)
    inverse_key = [None]*26
    inverse_count = [0]*26
    for n in range(26):
        inverse_key[n] = []
        for i in range(len(key_code)):
            if key_code[i] == n:
                inverse_key[n].append(i)
                inverse_count[n] += 1
    code = []
    for n in range(26):
        if inverse_count[n] is 0: continue
        index = offset = 0
        while inverse_key[n][index]+offset < len(plain) :
            c = plain[ inverse_key[n][index]+offset ]
            code.append(c)
            index += 1
            if index >= inverse_count[n]:
                index = 0
                offset += len(key_code)
    codetext = convert_to_string(code)
    display = display_transposition_block(plaintext,len(key_code))        
    return [codetext,display]

def myszkowski_decode(codetext,key):
    """
    decode string codetext with string key as myszkowski
    transposition. Output plaintext string.
    """
    code = convert_string(codetext)
    key_code = convert_string(key)
    inverse_key = [None]*26
    inverse_count = [0]*26
    for n in range(26):
        inverse_key[n] = []
        for i in range(len(key_code)):
            if key_code[i] == n:
                inverse_key[n].append(i)
                inverse_count[n] += 1
    plain = [None]*len(code)
    pos = 0
    for n in range(26):
        if inverse_count[n] is 0: continue
        index = offset = 0
        while inverse_key[n][index]+offset < len(code) :
            plain[ inverse_key[n][index]+offset ] = code[pos]
            pos += 1
            index += 1
            if index >= inverse_count[n]:
                index = 0
                offset += len(key_code)
    plaintext = convert_to_string(plain)
    display = display_transposition_block(plaintext,len(key_code))            
    return [plaintext,display]

def redefence_key_convert(key,start_row):
    """
    input key string and starting row number, relative to
    first row being 1 (not 0). Output alphabetic Myszkowski key.
    """
    ext_key = key
    for i in range(len(key)-2,0,-1):
        ext_key += key[i]
    final_key = ext_key[ start_row-1: ]+ext_key[ : start_row-1]
    my_key = ""
    for c in final_key:
        my_key += chr(ord(c)-ord('1')+ord('A'))
    return my_key

def redefence_encode(plaintext,key,start_row):
    """
    input plaintext and key string and starting row number, relative to
    first row being 1 (not 0). Output redefence codetext.
    """
    my_key = redefence_key_convert(key,start_row)
    codetext = myszkowski_encode(plaintext,my_key)[0]
    return codetext

def redefence_decode(codetext,key,start_row):
    """
    input codetext and key string and starting row number, relative to
    first row being 1 (not 0). Output redefence plaintext.
    """
    my_key = redefence_key_convert(key,start_row)
    plaintext = myszkowski_decode(codetext,my_key)[0]
    return plaintext

#Amsco routines
def amsco_setup(text_len,key_len,first_entry):
    """
    input integers text_len and key_len, and first_entry flag --
    0 if starting with single letter or 1 if starting with letter pair.
    Output number of rows and also pair_map showing which cells have 0,1 or 2 entries.
    """
    row_start = first_entry
    pair_map = [None]*key_len
    for n in range(key_len):
        pair_map[n] = []
    count = row = 0
    while count < text_len:
        parity = row_start
        row_start ^= 1
        for col in range(key_len):
            if count >= text_len:
                pair_map[col ] += [0]
            elif parity :
                pair_map[col] += [2]
                count += 2
            else:
                pair_map[col] += [1]
                count += 1
            parity ^= 1
        row += 1
    if count > text_len: #last cell not full
        for i in range(key_len-1,-1,-1):
            if pair_map[i][row-1] == 2:
                pair_map[i][row-1] -= 1
                break
    return [row,pair_map]

def display_amsco_array(plaintext,key_len,first_entry):
    """
    input string plaintext, integer key_len, and flag first_entry (0=single,1 = pair)
    return the corresponding amsco array.
    """
    plain= convert_string(plaintext)
    result = amsco_setup(len(plain),key_len,first_entry)
    numb_rows = result[0]
    pair_map = result[1]
    plain = convert_to_string(plain)
    array = ""
    index = 0
    for row in range(numb_rows):
        for col in range(key_len):
            if pair_map[col][row] == 1:
                array += plain[index]+"  "
                index += 1
            elif pair_map[col][row] == 2:
                array += plain[index:index+2]+" "
                index += 2
            else: break
        array += "\n"
    array += "\n"
    return array

def amsco_encode(plaintext,key,first_entry):
    """
    Input a plaintext string, a key string (either alphabetic, or as a string
    of integers separated by blanks) and flag first_entry (0 for single letter, 1 for pair).
    Output Amsco encoded codetext string.
    """
    plain = convert_string(plaintext)
    offset = get_hat_offset(key)
    numb_cols = len(offset)
    result = amsco_setup(len(plain),numb_cols,first_entry)
    numb_rows = result[0]
    pair_map = result[1]
    array  = [None]*numb_rows
    for n in range(numb_rows):
        array[n] = [None]*numb_cols
    index = 0
    for row in range(numb_rows):
        for col in range(numb_cols):
            if pair_map[col][row] == 2:
                array[row][col] = plain[index:index+2]
                index += 2
            elif pair_map[col][row] == 1:
                array[row][col] = [plain[index]]
                index += 1
            else: break
    code = []
    for n in range(numb_cols):
        for row in range(numb_rows):
            if array[row][ offset[n] ]:
                code += array[row][ offset[n] ]
    codetext = convert_to_string(code)
    display = display_amsco_array(plaintext,numb_cols,first_entry)
    return [codetext,display]

def amsco_decode(codetext,key,first_entry):
    """
    Input a codetext string, a key string (either alphabetic, or as a string
    of integers separated by blanks) and flag first_entry (0 for single letter, 1 for pair).
    Output Amsco decoded plaintext string.
    """
    code = convert_string(codetext)
    offset = get_hat_offset(key)
    numb_cols = len(offset)
    result = amsco_setup(len(code),numb_cols,first_entry)
    numb_rows = result[0]
    pair_map = result[1]
    array  = [None]*numb_rows
    for n in range(numb_rows):
        array[n] = [None]*numb_cols
    index = 0
    for n in range(numb_cols):
        col = offset[n]
        for row in range(numb_rows):
            if pair_map[col][row] == 2:
                array[row][col] = code[index:index+2]
                index += 2
            elif pair_map[col][row] == 1:
                array[row][col] = [code[index]]
                index += 1
            else: break
    plain = []
    index = row = col = 0
    while index < len(code):
        plain += array[row][ col ]
        index += len( array[row][col] )
        col += 1
        if col == numb_cols:
            row += 1
            col = 0
    plaintext = convert_to_string(plain)
    display = display_amsco_array(plaintext,numb_cols,first_entry)    
    return [plaintext,display]

# Grille routines
def turn_grille(key,grille_width):
    """
    intput list of key integers and grille_width integer.
    return list of new key integers from 90 degree rotation.
    """
    nkey = []
    for pos in key:
        row = int( pos/grille_width)
        col = pos % grille_width
        nkey.append( col*grille_width + grille_width -row -1 )
    nkey.sort()
    return nkey

def grille_encode(plaintext,key):
    """
    input strings plaintext and key. key is string of positions (start = 1) where
    the grille is open, separated by blanks. Return grille encoded codetext string.
    """
    plain = convert_string(plaintext)
    grille_width = int(sqrt(len(plain)))
    if grille_width * grille_width <> len(plain):
        print "Plaintext doesn't fit into square!"
        return "ERROR"
    nkey = []
    for pos in key.split():
        nkey.append( int(pos)-1)
    code = [0]*len(plain)
    sq = [[],[],[],[],[]]
    for n in range(4):
        sq[n] = [-1]*len(plain)
    if grille_width & 1:
        center = int(grille_width/2)
        center += grille_width*center
        try:
            x = nkey.index(center)
            nkey.pop(x)
        except ValueError:
            pass
        code[center] = plain[center]
        for n in range(4):
            sq[n][center]=plain[center]
    else : center = -1
    index = 0
    for i in range(4):
        for pos in nkey:
            code[pos] = plain[index]
            sq[i][pos] = plain[index]
            index += 1
            if index == center : index += 1
        nkey = turn_grille(nkey,grille_width)
    codetext = convert_to_string(code)
    return [codetext,sq]

def grille_decode(codetext,key):
    """
    input strings codetext and key. key is string of positions (start = 1) where
    the grille is open, separated by blanks. Return grille decoded codetext string.
    """
    code = convert_string(codetext)
    grille_width = int(sqrt(len(code)))
    if grille_width * grille_width <> len(code):
        print "codetext doesn't fit into square!"
        return "ERROR"
    nkey = []
    for pos in key.split():
        nkey.append( int(pos)-1)
    plain = [0]*len(code)
    if grille_width & 1:
        center = int(grille_width/2)
        center += grille_width*center
        try:
            x = nkey.index(center)
            nkey.pop(x)
        except ValueError:
            pass
        plain[center] = code[center]
    else: center = -1
    index = 0
    for i in range(4):
        for pos in nkey:
            plain[index] = code[pos]
            index += 1
            if index == center: index += 1
        nkey = turn_grille(nkey,grille_width)
    plaintext = convert_to_string(plain)
    return plaintext

#Swagman routines
def swagman_encode(plaintext,key):
    """
    input string plaintext, and list of strings 'key', one
    key string for each key row. output swagman encrypted
    codetext string.
    """
    plain = convert_string(plaintext)
    numb_rows = len(key)
    numb_cols = int(len(plain)/numb_rows)
    xtra = len(plain) - numb_cols*numb_rows
    if xtra : #add nulls
        plain += [ord('x')-ord('a')]*(numb_rows-xtra)
        numb_cols += 1
    nkey = [None]*numb_rows
    for row in range(numb_rows):
        nkey[row] = [ord(x)-ord('1') for x in key[row] ]
    inverse_key = [None]*numb_rows
    for n in range(numb_rows):
        inverse_key[n] = [None]*numb_rows
    for col in range(numb_rows):
        for row in range(numb_rows):
            for k in range(numb_rows):
                if nkey[row][col] == k:
                    inverse_key[k][col] = row
                    break
    code = []
    for col in range(numb_cols):
        for row in range(numb_rows):
            pos = inverse_key[row][col % numb_rows]
            code.append( plain[ col+pos*numb_cols])
    codetext = convert_to_string(code)
    return codetext

def swagman_decode(codetext,key):
    """
    input string codetext, and list of strings 'key', one
    key string for each key row. output swagman encrypted
    codetext string.
    """
    code = convert_string(codetext)
    numb_rows = len(key)
    numb_cols = int(len(code)/numb_rows)
    xtra = len(code) - numb_cols*numb_rows
    if xtra :
        print "Ciphertext not mutiple of key length!"
        return "ERROR"
    nkey = [None]*numb_rows
    for row in range(numb_rows):
        nkey[row] = [ord(x)-ord('1') for x in key[row] ]
    inverse_key = [None]*numb_rows
    for n in range(numb_rows):
        inverse_key[n] = [None]*numb_rows
    for col in range(numb_rows):
        for row in range(numb_rows):
            for k in range(numb_rows):
                if nkey[row][col] == k:
                    inverse_key[k][col] = row
                    break
    plain = [None]*len(code)
    index = 0
    for col in range(numb_cols):
        for row in range(numb_rows):
            pos = inverse_key[row][col % numb_rows]
            plain[ col+pos*numb_cols] = code[index]
            index += 1
    plaintext = convert_to_string(plain)
    return plaintext

#homophonic routines
def homophonic_encode(plaintext,key, line_length = 22):
    """
    homophonic encryption of the plaintext string by the key string.
    return string of cipher digit pairs broken into lines of length
    line_length.
    """
    shift  = [1,26,51,76]
    plain = convert_string(plaintext)
    #convert to range 0-24, with i and j same
    for i in range(len(plain)):
        if plain[i] >= ord('j')-ord('a'):
            plain[i] -= 1
    key_code = convert_string(key)
    if len(key_code) != 4:
        print "Key not 4 letters!"
        return
    #convert key same way
    for i in range(4):
        if key_code[i] >= ord('j')-ord('a'):
            key_code[i] -= 1
    code = []
    for c in plain:
        x = randrange(4)
        n = (25+c-key_code[x])%25 + shift[x]
        code.append(n)
    code_text = []
    ct = 0
    for n in code:
        if n == 100:
            code_text.append("00")
        elif n < 10:
            code_text.append("0%d" % n)
        else:
            code_text.append("%d" % n)
        ct += 1
#         if (ct % line_length) == 0:
#             code_text.append("\n")
    return ''.join(code_text)

def homophonic_decode(codetext,key):
    """
    homophonic decryption of the cipherdigit string by the key string.
    return lower case plaintext string
    """
    shift  = [1,26,51,76]
    key_code = convert_string(key)
    if len(key_code) != 4:
        print "Key not 4 letters!"
        return
    #convert key to range 0 to 24, with i and j same
    for i in range(4):
        if key_code[i] >= ord('j')-ord('a'):
            key_code[i] -= 1
    code = convert_numb_string(codetext)
    if len(code) & 1:
        #print "Odd numbers of digits!"
        return "ERROR, Odd number of digits"
    plain = []
    for i in range(0,len(code),2):
        n = 10*code[i]+code[i+1]
        if n is 0:
            n = 100
        if n < shift[1]:
            c = (25+n-shift[0]+key_code[0]) % 25
        elif n < shift[2]:
            c = (25+n-shift[1]+key_code[1]) % 25
        elif n < shift[3]:
            c = (25+n-shift[2]+key_code[2]) % 25
        else:
            c = (25+n-shift[3]+key_code[3]) % 25
        if c >= ord('j')-ord('a'):
            c += 1
        plain.append(c)
    plaintext = convert_to_string(plain)
    return plaintext

#tri-square routines
def trisquare_encode(plaintext,left_key,top_key,middle_key,lroute = 3,troute = 0,mroute = 2,use6x6=0):
    """
    given plaintext string and 3 key strings, return codetext string.
    default routes are vertical, horizontal, and spiral
    """
    if use6x6: length = 6
    else : length = 5
    leftsquare = get_keysquare(left_key,lroute,use6x6)
    topsquare = get_keysquare(top_key,troute,use6x6)
    middlesquare = get_keysquare(middle_key,mroute,use6x6)
    plain = convert_string(plaintext, noJ=1,use6x6=use6x6 )
    if len(plain) & 1 :
        print "Odd number of plaintext letters!"
        return "ERROR"
    code = []
    for i in range(0,len(plain),2):
        cl = plain[i]
        cr = plain[i+1]
        clc = find_keysquare_coordinates(cl,leftsquare,use6x6)
        crc = find_keysquare_coordinates(cr,topsquare,use6x6)
        if clc[0] == -1 or crc[0] == -1:
            print "Program Bug!"
            return "ERROR"
        lrow = randrange(length)
        tcol = randrange(length)
        ltr1 = leftsquare[lrow][ clc[1] ]
        ltr2 = middlesquare[ clc[0] ][ crc[1] ]
        ltr3 = topsquare[ crc[0] ][ tcol ]
        s = convert_to_string( [ltr1,ltr2,ltr3 ],use6x6=use6x6 )
        code.append(s.upper() )
    codetext = ''.join(code)
    return codetext

def trisquare_decode(codetext,left_key,top_key,middle_key,lroute = 3,troute = 0,mroute = 2,use6x6=0):
    """
    given codetext string and 3 key strings, return plaintext string.
    default routes are vertical, horizontal, and spiral
    """
    leftsquare = get_keysquare(left_key,lroute,use6x6)
    topsquare = get_keysquare(top_key,troute,use6x6)
    middlesquare = get_keysquare(middle_key,mroute,use6x6)
    code = convert_string(codetext,noJ=1,use6x6 = use6x6)
    if len(code) % 3 :
        print "Code length not multiple of 3!"
        return "ERROR"
    plain = []
    for i in range(0,len(code),3):
        cl = code[i]
        cm = code[i+1]
        ct = code[i+2]
        clc = find_keysquare_coordinates(cl,leftsquare,use6x6)
        cmc = find_keysquare_coordinates(cm,middlesquare,use6x6)
        ctc = find_keysquare_coordinates(ct,topsquare,use6x6)
        if clc[0] == -1 or cmc[0] == -1 or ctc[0] == -1:
            print "Program Bug!"
            return "ERROR"
        ltr1 = leftsquare[cmc[0] ][ clc[1] ]
        ltr2 = topsquare[ ctc[0] ][ cmc[1] ]
        s = convert_to_string( [ltr1,ltr2 ], use6x6 = use6x6 )
        plain.append( s )
    plaintext = ''.join(plain)
    return plaintext

#Gromark routines
def get_k2m_key(key, lr_order = 0):
    """
    input key word(s) string, return complete k2m alphbet string.
    Take off key in alphabetical order unless lr_order is not 0.
    In that case take off in left-right order.
    """
    alpha = 'abcdefghijklmnopqrstuvwxyz'
    #remove duplicated letters from key
    key = key.lower()
    small_key = ""
    for c in key:
        if c not in small_key:
            small_key = small_key+c
    k2m_key = small_key
    #extend to complete alphabet
    for c in alpha:
        if c not in k2m_key:
            k2m_key = k2m_key+c
    if lr_order:
        small_key = alpha[ :len(small_key)]
    k2m_key = columnar_encode(k2m_key, small_key)[0]
    return k2m_key

def get_gromark_chain(primer, n):
    """
    input string of primer digits and number n, return gromark chain
    of length n
    """
    plist = [ ord(c)-ord('0') for c in primer]
    chain = plist
    lenp = len(plist)
    for i in range(lenp,n):
        chain.append( ( chain[ i-lenp ] + chain[i-lenp+1] )%10 )
    return chain

def gromark_encode(key,primer,plaintext,lr_order = 0):
    """
    input key string, string of primer digits, and plaintext string.
    return codetext string and chain check-digit.
    Take off key in alphabetical order unless lr_order is not 0.
    In that case take off in left-right order.
    """
    k2m_key = get_k2m_key(key, lr_order)
    save_key = k2m_key
    k2m_key = convert_string(k2m_key)
    plain = convert_string(plaintext)
    chain = get_gromark_chain(primer,len(plain))
    code = [ k2m_key[(plain[i]+chain[i])%26] for i in range(len(plain)) ]
    codetext = convert_to_string(code)
    return [ codetext, chain[-1] ,chain,save_key]

def gromark_decode(key,primer,codetext,lr_order=0):
    """
    input key string, string of primer digits, and codetext string.
    return plaintext string.
    Take off key in alphabetical order unless lr_order is not 0.
    In that case take off in left-right order.
    """
    k2m_key = get_k2m_key(key, lr_order)
    save_key = k2m_key
    k2m_key = convert_string(k2m_key)
    code = convert_string(codetext)
    chain = get_gromark_chain(primer,len(code))
    plain = [ (26+k2m_key.index( code[i] )-chain[i])%26 for i in range(len(code))]
    plaintext = convert_to_string(plain)
    return [plaintext, chain[-1],chain,save_key]

def periodic_gromark_primer(key,lr_order = 0):
    """
    special for ACA display purposes
    given key string, return primer string
    Take off key in alphabetical order unless lr_order is not 0.
    In that case take off in left-right order.
    """
    k2m_key = get_k2m_key(key, lr_order)
    k2m_key = convert_string(k2m_key)
    #get transposition key
    offset = get_hat_offset(key)
    lprimer = offset_to_key(offset)
    #change from 0 to 1 as lowest index and convert to ASCII digits
    nprimer = [chr( ( x+1)%10 +ord('0') ) for x in lprimer]
    #convert to string of digits
    primer = ''.join(nprimer)
    nkey = convert_string(key)    
    indices = [ k2m_key.index( nkey[n] ) for n in range(len(lprimer))]
    return [primer,indices]
    
def periodic_gromark_encode(key,plaintext,lr_order = 0):
    """
    given key and plaintext strings, return codetext string and check-digit.
    Take off key in alphabetical order unless lr_order is not 0.
    In that case take off in left-right order.
    """
    k2m_key = get_k2m_key(key, lr_order)
    save_key = k2m_key
    k2m_key = convert_string(k2m_key)
    plain = convert_string(plaintext)
    #get transposition key
    offset = get_hat_offset(key)
    lprimer = offset_to_key(offset)
    #change from 0 to 1 as lowest index and convert to ASCII digits
    nprimer = [chr( ( x+1)%10 +ord('0') ) for x in lprimer]
    #convert to string of digits
    primer = ''.join(nprimer)
    chain = get_gromark_chain(primer,len(plain))
    nkey = convert_string(key)
    lenp  = len(primer)
    code = []
    n = index = 0
    for i in range(len(plain)):
        c1 = k2m_key.index( nkey[index] )
        c = k2m_key[ (c1+plain[i]+chain[i]) % 26]
        code.append(c)
        n += 1
        if n == lenp:
            n = 0
            index = (index+1) % lenp
    codetext = convert_to_string(code)
    return [codetext, chain[-1], chain, save_key ]

def periodic_gromark_decode(key,codetext,lr_order = 0):
    """
    given key and codetext strings, return codetext string.
    Take off key in alphabetical order unless lr_order is not 0.
    In that case take off in left-right order.
    """
    k2m_key = get_k2m_key(key, lr_order)
    save_key = k2m_key
    k2m_key = convert_string(k2m_key)
    code = convert_string(codetext)
    #get transposition key
    offset = get_hat_offset(key)
    lprimer = offset_to_key(offset)
    #change from 0 to 1 as lowest index and convert to ASCII digits
    nprimer = [chr( ( x+1)%10 +ord('0') ) for x in lprimer]
    #convert to string of digits
    primer = ''.join(nprimer)
    chain = get_gromark_chain(primer,len(code))
    nkey = convert_string(key)
    lenp  = len(primer)
    plain = []
    n = index = 0
    for i in range(len(code)):
        c1 = k2m_key.index( nkey[index] )
        c = (52+k2m_key.index( code[i] )-chain[i]-c1) % 26
        plain.append(c)
        n += 1
        if n == lenp:
            n = 0
            index = (index+1) % lenp
    plaintext = convert_to_string(plain)
    return [plaintext,chain[-1], chain, save_key]

#Playfair and seriated Playfair routines
def seriated_playfair_encode(plaintext,key,period,route = 0,use6x6=0):
    """
    Input strings plaintext and key, and integer period. Default route is horizontal.
    Output seriated Playfair codetext string, but not broken into pairs.
    (Use output_code_groups to format the output).
    insert nulls as needed.
    """
    plain = convert_string(plaintext,noJ = 1,use6x6=use6x6)
    if use6x6 : length = 6
    else: length = 5
    #insert nulls
    redo_flag = 1
    made_even_flag = 0
    while redo_flag:
        le = len(plain)
        left_over = le % (2*period)
        redo_flag = 0
        pos = 0
        while pos < le - left_over:
            for i in range(period):
                if plain[pos+i] == plain[pos+i+period]:
                    nul = ord('x')-ord('a')
                    if plain[pos+i] == nul: nul += 2
                    plain[pos+i+period:pos+i+period] = [nul]
                    redo_flag = 1
                    if made_even_flag:
                        plain.pop(-1) # remove added element
                        made_even_flag = 0
                    #print "Added null"
                    break
            if redo_flag : break
            pos += 2*period
        if redo_flag : continue
        if left_over & 1 :
            plain.append(ord('z')-ord('a'))
            made_even_flag = 1
            redo_flag = 1
            continue #recalculate left_over
        if left_over:
            pos = le - left_over
            for i in range(left_over/2):
                if plain[pos+i] == plain[pos+i+left_over/2]:
                    nul = ord('x')-ord('a')
                    if plain[pos+i] == nul: nul += 2
                    plain[pos+i+left_over/2:pos+i+left_over/2] = [nul]
                    redo_flag = 1
                    #print "Added null"
                    if made_even_flag:
                        plain.pop(-1) # remove added element
                        made_even_flag = 0                  
                    break
    keysquare = get_keysquare(key,route,use6x6=use6x6)
    le = len(plain)
    left_over = le % (2*period)
    pos = 0
    code = [None]*le
    while pos < le - left_over:
        for i in range(period):
            cl = plain[pos+i]
            cr = plain[pos+i+period]
            clc = find_keysquare_coordinates(cl,keysquare,use6x6=use6x6)
            crc = find_keysquare_coordinates(cr,keysquare,use6x6=use6x6)
            if clc[0] == -1 or crc[0] == -1:
                print "Program Bug!"
                return "ERROR"
            if clc[0] == crc[0]:
                ltr1 = keysquare[ clc[0] ][ (clc[1]+1)% length ]
                ltr2 = keysquare[ crc[0] ][ (crc[1]+1)% length ]
            elif clc[1] == crc[1]:
                ltr1 = keysquare[ (clc[0]+1)% length ][ clc[1] ]
                ltr2 = keysquare[ (crc[0]+1)% length ][ crc[1] ]
            else:
                ltr1 = keysquare[ clc[0] ][ crc[1] ]
                ltr2 = keysquare[ crc[0] ][ clc[1] ]
            code[pos+i] = ltr1
            code[pos+i+period] = ltr2
        pos += 2*period
    if left_over:
        pos = le - left_over
        for i in range(left_over/2):
            cl = plain[pos+i]
            cr = plain[pos+i+left_over/2]
            clc = find_keysquare_coordinates(cl,keysquare,use6x6=use6x6)
            crc = find_keysquare_coordinates(cr,keysquare,use6x6=use6x6)
            if clc[0] == -1 or crc[0] == -1:
                print "Program Bug!"
                return "ERROR"
            if clc[0] == crc[0]:
                ltr1 = keysquare[ clc[0] ][ (clc[1]+1)% length ]
                ltr2 = keysquare[ crc[0] ][ (crc[1]+1)% length ]
            elif clc[1] == crc[1]:
                ltr1 = keysquare[ (clc[0]+1)% length ][ clc[1] ]
                ltr2 = keysquare[ (crc[0]+1)% length ][ crc[1] ]
            else:
                ltr1 = keysquare[ clc[0] ][ crc[1] ]
                ltr2 = keysquare[ crc[0] ][ clc[1] ]
            code[pos+i] = ltr1
            code[pos+i+left_over/2] = ltr2
    codetext = convert_to_string(code,use6x6=use6x6)
    return codetext

def seriated_playfair_decode(codetext,key,period,route = 0,use6x6=0):
    """
    Input strings codetext and key, and integer period. Default route is horizontal.
    Output seriated Playfair plaintext string.
    """
    code = convert_string(codetext,noJ = 1,use6x6=use6x6)
    keysquare = get_keysquare(key,route,use6x6=use6x6)
    if use6x6: length = 6
    else : length = 5
    le = len(code)
    left_over = le % (2*period)
    if left_over & 1:
        print "Odd number of left over letters!"
        return "ERROR"
    pos = 0
    plain = [None]*le
    while pos < le - left_over:
        for i in range(period):
            cl = code[pos+i]
            cr = code[pos+i+period]
            clc = find_keysquare_coordinates(cl,keysquare,use6x6=use6x6)
            crc = find_keysquare_coordinates(cr,keysquare,use6x6=use6x6)
            if clc[0] == -1 or crc[0] == -1:
                print "Program Bug!"
                return "ERROR"
            if clc[0] == crc[0]:
                ltr1 = keysquare[ clc[0] ][ (clc[1]+(length-1))% length ]
                ltr2 = keysquare[ crc[0] ][ (crc[1]+(length-1))% length ]
            elif clc[1] == crc[1]:
                ltr1 = keysquare[ (clc[0]+(length-1))% length ][ clc[1] ]
                ltr2 = keysquare[ (crc[0]+(length-1))% length ][ crc[1] ]
            else:
                ltr1 = keysquare[ clc[0] ][ crc[1] ]
                ltr2 = keysquare[ crc[0] ][ clc[1] ]
            plain[pos+i] = ltr1
            plain[pos+i+period] = ltr2
        pos += 2*period
    if left_over:
        pos = le - left_over
        for i in range(left_over/2):
            cl = code[pos+i]
            cr = code[pos+i+left_over/2]
            clc = find_keysquare_coordinates(cl,keysquare,use6x6=use6x6)
            crc = find_keysquare_coordinates(cr,keysquare,use6x6=use6x6)
            if clc[0] == -1 or crc[0] == -1:
                print "Program Bug!"
                return "ERROR"
            if clc[0] == crc[0]:
                ltr1 = keysquare[ clc[0] ][ (clc[1]+(length-1))% length ]
                ltr2 = keysquare[ crc[0] ][ (crc[1]+(length-1))% length ]
            elif clc[1] == crc[1]:
                ltr1 = keysquare[ (clc[0]+ (length-1))% length ][ clc[1] ]
                ltr2 = keysquare[ (crc[0]+(length-1))% length ][ crc[1] ]
            else:
                ltr1 = keysquare[ clc[0] ][ crc[1] ]
                ltr2 = keysquare[ crc[0] ][ clc[1] ]
            plain[pos+i] = ltr1
            plain[pos+i+left_over/2] = ltr2
    plaintext = convert_to_string(plain,use6x6=use6x6)
    return plaintext

def playfair_encode(plaintext,key,route = 0,use6x6=0):
    """
    Input strings plaintext and key. Default route is horizontal.
    Output Playfair codetext string, but not broken into pairs.
    (Use output_code_groups to format the output).
    insert nulls as needed.
    """
    return seriated_playfair_encode(plaintext,key,1,route,use6x6=use6x6)

def playfair_decode(codetext,key,route = 0,use6x6=0):
    """
    Input strings codetext and key. Default route is horizontal.
    Output Playfair plaintext string.
    """
    return seriated_playfair_decode(codetext,key,1,route,use6x6=use6x6)

#Two square and four square routines
def two_square_encode(plaintext,left_key,right_key,lroute = 0,rroute = 0,use6x6=0):
    """
    input strings: plaintext,left key, and right key. Default routes are
    horizontal. Output two-square codetext string, not broken into pairs. (use
    output_code_groups for that)
    """
    plain = convert_string(plaintext,noJ = 1,use6x6=use6x6)
    if len(plain) & 1 :
        print "Odd number of plaintext letters!"
        return "ERROR"
    lsquare = get_keysquare(left_key,lroute,use6x6=use6x6)
    rsquare = get_keysquare(right_key,rroute,use6x6=use6x6)
    code = []
    for i in range(0,len(plain),2):
        cl = plain[i]
        cr = plain[i+1]
        clc = find_keysquare_coordinates(cl,lsquare,use6x6=use6x6)
        crc = find_keysquare_coordinates(cr,rsquare,use6x6=use6x6)
        if clc[0] == -1 or crc[0] == -1:
            print "Program Bug!"
            return "ERROR"
        if clc[0] == crc[0]:
            ltr1 = cr
            ltr2 = cl
        else:
            ltr1 = rsquare[ clc[0] ][ crc[1] ]
            ltr2 = lsquare[ crc[0] ][ clc[1] ]
        s = convert_to_string( [ltr1,ltr2],use6x6=use6x6 )
        code.append(s)
    codetext = ''.join(code)
    return codetext

def two_square_decode(codetext,left_key,right_key,lroute = 0,rroute = 0,use6x6=0):
    """
    input strings: codetext,left key, and right key. Default routes are
    horizontal. Output two-square plaintext string.
    """
    code = convert_string(codetext,noJ=1,use6x6=use6x6)
    if len(code) & 1 :
        print "Odd number of plaintext letters!"
        return "ERROR"
    lsquare = get_keysquare(left_key,lroute,use6x6=use6x6)
    rsquare = get_keysquare(right_key,rroute,use6x6=use6x6)
    plain = []
    for i in range(0,len(code),2):
        cl = code[i]
        cr = code[i+1]
        #look up coordinates as before, but with squares reversed
        clc = find_keysquare_coordinates(cl,rsquare,use6x6=use6x6)
        crc = find_keysquare_coordinates(cr,lsquare,use6x6=use6x6)
        if clc[0] == -1 or crc[0] == -1:
            print "Program Bug!"
            return "ERROR"
        if clc[0] == crc[0]:
            ltr1 = cr
            ltr2 = cl
        else:
            ltr1 = lsquare[ clc[0] ][ crc[1] ]
            ltr2 = rsquare[ crc[0] ][ clc[1] ]
        s = convert_to_string( [ltr1,ltr2], use6x6=use6x6 )
        plain.append(s)
    plaintext = ''.join(plain)
    return plaintext

def four_square_encode(plaintext,left_key,right_key,lroute = 0,rroute = 0,use6x6=0):
    """
    input strings: plaintext,left key, and right key. Default routes are
    horizontal. Output four-square codetext string, not broken into pairs. (use
    output_code_groups for that)
    """
    plain = convert_string(plaintext,noJ=1,use6x6=use6x6)
    if len(plain) & 1 :
        print "Odd number of plaintext letters!"
        return "ERROR"
    lsquare = get_keysquare(left_key,lroute,use6x6=use6x6)
    rsquare = get_keysquare(right_key,rroute,use6x6=use6x6)
    fixed_square = get_keysquare("A",use6x6=use6x6)
    code = []
    for i in range(0,len(plain),2):
        cl = plain[i]
        cr = plain[i+1]
        clc = find_keysquare_coordinates(cl,fixed_square,use6x6=use6x6)
        crc = find_keysquare_coordinates(cr,fixed_square,use6x6=use6x6)
        ltr1 = rsquare[ clc[0] ][ crc[1] ]
        ltr2 = lsquare[ crc[0] ][ clc[1] ]
        s = convert_to_string( [ltr1,ltr2],use6x6=use6x6 )
        code.append(s)
    codetext = ''.join(code)
    return codetext

def four_square_decode(codetext,left_key,right_key,lroute = 0,rroute = 0,use6x6=0):
    """
    input strings: codetext,left key, and right key. Default routes are
    horizontal. Output four-square plaintext string.
    """
    code = convert_string(codetext,noJ=1,use6x6=use6x6)
    if len(code) & 1 :
        print "Odd number of plaintext letters!"
        return "ERROR"
    lsquare = get_keysquare(left_key,lroute,use6x6=use6x6)
    rsquare = get_keysquare(right_key,rroute,use6x6=use6x6)
    fixed_square = get_keysquare("A",use6x6=use6x6)
    plain = []
    for i in range(0,len(code),2):
        cl = code[i]
        cr = code[i+1]
        clc = find_keysquare_coordinates(cl,rsquare,use6x6=use6x6)
        crc = find_keysquare_coordinates(cr,lsquare,use6x6=use6x6)
        if clc[0] == -1 or crc[0] == -1:
            print "Program Bug!"
            return "ERROR"
        ltr1 = fixed_square[ clc[0] ][ crc[1] ]
        ltr2 = fixed_square[ crc[0] ][ clc[1] ]
        s = convert_to_string( [ltr1,ltr2],use6x6=use6x6 )
        plain.append(s)
    plaintext = ''.join(plain)
    return plaintext

#bifid, trifid, digrafid routines
def bifid_encode(plaintext,key,period,route=0,use6x6=0):
    """
    Input strings plaintext and key, and integer period. Default route is horizontal.
    Output unformatted Bifid codetext string( Use output_code_groups to format the output).
    """
    plain = convert_string(plaintext,noJ = 1,use6x6=use6x6)
    keysquare = get_keysquare(key,route,use6x6=use6x6)
    workspace = [None]*(2*period)
    le = len(plain)
    if period < le:
        offset = period
    else:
        offset = le
    index = pos = 0
    code = []
    for c in plain:
        co = find_keysquare_coordinates(c,keysquare,use6x6=use6x6)
        workspace[index] = co[0]
        workspace[index+offset] = co[1]
        index += 1
        if index == offset: #workspace full
            for i in range(0,2*offset,2):
                code.append( keysquare[ workspace[i] ][ workspace[ i+1] ])
            index = 0
            pos += offset
            if period >= le-pos:
                offset = le - pos
    codetext = convert_to_string(code,use6x6=use6x6)
    return codetext

def bifid_decode(codetext,key,period,route=0,use6x6=0):
    """
    Input strings codetext and key, and integer period. Default route is horizontal.
    Output Bifid plaintext string.
    """
    code = convert_string(codetext,noJ = 1,use6x6=use6x6)
    keysquare = get_keysquare(key,route,use6x6=use6x6)
    workspace = [None]*(2*period)
    le = len(code)
    if period < le:
        offset = period
    else:
        offset = le
    index = pos = 0
    plain = []
    for c in code:
        co = find_keysquare_coordinates(c,keysquare,use6x6=use6x6)
        workspace[index:index+2] = co
        index += 2
        if index == 2*offset: #workspace full
            for i in range(offset):
                plain.append( keysquare[ workspace[i] ][ workspace[ i+offset] ])
            index = 0
            pos += offset
            if period >= le-pos:
                offset = le - pos
    plaintext = convert_to_string(plain,use6x6=use6x6)
    return plaintext

def cm_bifid_encode(plaintext,left_key,right_key,period,lroute=0,rroute=0,use6x6=0):
    """
    Input strings plaintext and left_key, right_key, and integer period. Default routes horizontal.
    Output unformatted CM Bifid codetext string( Use output_code_groups to format the output).
    """
    plain = convert_string(plaintext,noJ = 1,use6x6=use6x6)
    lkeysquare = get_keysquare(left_key,lroute,use6x6=use6x6)
    rkeysquare = get_keysquare(right_key,rroute,use6x6 = use6x6)
    workspace = [None]*(2*period)
    le = len(plain)
    if period < le:
        offset = period
    else:
        offset = le
    index = pos = 0
    code = []
    for c in plain:
        co = find_keysquare_coordinates(c,lkeysquare,use6x6=use6x6)
        workspace[index] = co[0]
        workspace[index+offset] = co[1]
        index += 1
        if index == offset: #workspace full
            for i in range(0,2*offset,2):
                code.append( rkeysquare[ workspace[i] ][ workspace[ i+1] ])
            index = 0
            pos += offset
            if period >= le-pos:
                offset = le - pos
    codetext = convert_to_string(code,use6x6=use6x6)
    return codetext

def cm_bifid_decode(codetext,left_key,right_key,period,lroute=0,rroute=0,use6x6=0):
    """
    Input strings codetext left_key,right_key and integer period. Default routes horizontal.
    Output CM Bifid plaintext string.
    """
    code = convert_string(codetext,noJ = 1,use6x6=use6x6)
    lkeysquare = get_keysquare(left_key,lroute,use6x6=use6x6)
    rkeysquare = get_keysquare(right_key,rroute,use6x6 = use6x6)
    workspace = [None]*(2*period)
    le = len(code)
    if period < le:
        offset = period
    else:
        offset = le
    index = pos = 0
    plain = []
    for c in code:
        co = find_keysquare_coordinates(c,rkeysquare,use6x6=use6x6)
        workspace[index:index+2] = co
        index += 2
        if index == 2*offset: #workspace full
            for i in range(offset):
                plain.append( lkeysquare[ workspace[i] ][ workspace[ i+offset] ])
            index = 0
            pos += offset
            if period >= le-pos:
                offset = le - pos
    plaintext = convert_to_string(plain,use6x6=use6x6)
    return plaintext

def trifid_encode(plaintext,key,period):
    """
    Input strings plaintext and key, and integer period.
    Output unformatted trifid codetext string( Use output_code_groups to format the output).
    """
    plain = convert_string(plaintext,noJ = 0,yes_sharp = 1)
    key_array = get_key_array(key,'',yes_sharp = 1)
    workspace = [None]*(3*period)
    le = len(plain)
    if period < le:
        offset = period
    else:
        offset = le
    index = pos = 0
    code = []
    for c in plain:
        n = key_array.index(c)
        workspace[index] = int(n/9)
        m = n % 9
        workspace[index+offset] = int(m/3)
        workspace[index+2*offset] = m % 3
        index += 1
        if index == offset: #workspace full
            for i in range(0,3*offset,3):
                code.append( key_array[ workspace[i]*9+ workspace[i+1]*3+workspace[i+2] ])
            index = 0
            pos += offset
            if period >= le-pos:
                offset = le - pos
    codetext = convert_to_string(code)
    return codetext

def trifid_decode(codetext,key,period):
    """
    Input strings codetext and key, and integer period.
    Output trifid plaintext string.
    """
    code = convert_string(codetext,noJ = 0,yes_sharp=1)
    key_array = get_key_array(key,'',yes_sharp = 1)
    workspace = [None]*(3*period)
    le = len(code)
    if period < le:
        offset = period
    else:
        offset = le
    index = pos = 0
    plain = []
    for c in code:
        x = key_array.index(c)
        n = int(x/9)
        m = x % 9
        workspace[index:index+3] = [n,int(m/3),m%3]
        index += 3
        if index == 3*offset: #workspace full
            for i in range(offset):
                plain.append( key_array[ workspace[i]*9+workspace[ i+offset]*3\
                    +workspace[i+2*offset] ])
            index = 0
            pos += offset
            if period >= le-pos:
                offset = le - pos
    plaintext = convert_to_string(plain)
    return plaintext

def digrafid_encode(plaintext,horizontal_key,vertical_key,period):
    """
    Input strings plaintext and keys, and integer period.
    Output unformatted digrafid codetext string (Use output_code_groups to format the output).
    Note: period is for PAIRS of letters, not one at a time.
    """
    plain = convert_string(plaintext,noJ = 0,yes_sharp = 1)
    hkey = get_key_array(horizontal_key,'',yes_sharp = 1)
    vkey = get_key_array(vertical_key,'',yes_sharp = 1)
    workspace = [None]*(3*period)
    if len(plain) & 1: #add null
        plain.append(ord('x')-ord('a'))
    le = len(plain)
    if 2*period < le:
        offset = period
    else:
        offset = le/2
    index = pos = 0
    code = []
    for i in range(0,le,2):
        n = hkey.index(plain[i])
        row = int(n/9)
        left_digit = n % 9
        n = vkey.index(plain[i+1])
        col = int(n/9)
        right_digit = n % 9
        middle_digit = 3*row+col
        workspace[index] = left_digit
        workspace[index+offset] = middle_digit
        workspace[index+2*offset] = right_digit
        index += 1
        if index == offset: #workspace full
            for j in range(0,3*offset,3):
                hor_digit = workspace[j]
                n = workspace[j+1]
                row = int(n/3)
                col = n % 3
                code.append( hkey[hor_digit+9*row ])
                vert_digit = workspace[j+2]
                code.append( vkey[vert_digit+9*col] )
            index = 0
            pos += 2*offset # encoding pairs of letters
            if 2*period >= le-pos:
                offset = (le - pos)/2
    codetext = convert_to_string(code)
    return codetext

def digrafid_decode(codetext,horizontal_key,vertical_key,period):
    """
    Input strings codetext and keys, and integer period.
    Output digrafid plaintext string
    Note: period is for PAIRS of letters, not one at a time.
    """
    code = convert_string(codetext,noJ = 0,yes_sharp = 1)
    hkey = get_key_array(horizontal_key,'',yes_sharp = 1)
    vkey = get_key_array(vertical_key,'',yes_sharp = 1)
    workspace = [None]*(3*period)
    if len(code) & 1:
        print "Odd number of letters!"
        return "ERROR"
    le = len(code)
    if 2*period < le:
        offset = period
    else:
        offset = le/2
    index = pos = 0
    plain = []
    for i in range(0,le,2):
        n = hkey.index(code[i])
        row = int(n/9)
        left_digit = n % 9
        n = vkey.index(code[i+1])
        col = int(n/9)
        right_digit = n % 9
        middle_digit = 3*row+col
        workspace[index] = left_digit
        workspace[index+1] = middle_digit
        workspace[index+2] = right_digit
        index += 3
        if index == 3*offset: #workspace full
            for j in range(offset):
                hor_digit = workspace[j]
                n = workspace[j+offset]
                row = int(n/3)
                col = n % 3
                plain.append( hkey[hor_digit+9*row ])
                vert_digit = workspace[j+2*offset]
                plain.append( vkey[vert_digit+9*col] )
            index = 0
            pos += 2*offset # encoding pairs of letters
            if 2*period >= le-pos:
                offset = (le - pos)/2
    plaintext = convert_to_string(plain)
    return plaintext

#6x6 versions of ciphers: bifid

def bifid_6x6_encode(plaintext,key,period,route=0):
    """
    Input strings plaintext and key, and integer period. Default route is horizontal.
    Output unformatted 6x6 Bifid codetext string( Use output_code_groups to format the output).
    """
    return bifid_encode(plaintext,key,period,route=route,use6x6=1)

def bifid_6x6_decode(codetext,key,period,route=0):
    """
    Input strings codetext and key, and integer period. Default route is horizontal.
    Output 6x6 Bifid plaintext string.
    """
    return bifid_decode(codetext,key,period,route=route,use6x6=1)

#Phillips routines
def setup_squares(key,route,ptype):
    """
    input strings key, route and ptype ('R','C' or 'RC')
    output the coresponding 8 phillips squares
    """
    ks = get_keysquare(key,route)
    squares = [None]*8
    squares[0] = ks
    for n in range(1,8):
        squares[n] = [None]*5
        for i in range(5):
            squares[n][i]=[None]*5
    index = 1
    while index < 8:
        for swap_index in range(4):
            for cell in range(5):
                if cell==swap_index:
                    rindex = cell+1
                elif cell == swap_index+1:
                    rindex = cell-1
                else:
                    rindex = cell
                if ptype=='R':
                    squares[index][cell]=[squares[index-1][rindex][col] for col in range(5)]
                elif ptype=='C':
                    for row in range(5):
                        squares[index][row][cell] = squares[index-1][row][rindex]
                else:
                    for col in range(5):
                        if col==swap_index:
                            cindex = col+1
                        elif col == swap_index+1:
                            cindex = col-1
                        else:
                            cindex = col
                        squares[index][cell][col] = squares[index-1][rindex][cindex]
            index += 1
            if index == 8 : break
    return squares
    
def phillips_encode(plaintext,key,route=0,ptype='R'):
    """
    Input strings plaintext and key, default route is horizontal.
    default type is ordinary Phillips ( not C or RC)
    Output unformatted Phillips ciphertext string.
    """
    plain = convert_string(plaintext,noJ=1)
    squares = setup_squares(key,route,ptype)
    period = 8
    index = 0
    count = 0
    code = []
    for c in plain:
        co = find_keysquare_coordinates(c,squares[index])
        if co[0] == -1 :
            print "Program Bug!"
            return "ERROR"
        d = squares[index][ (co[0]+1)%5][ (co[1]+1)%5]
        code.append(d)
        count = count+1
        if count == 5:
            count = 0
            index = index+1
            if index == period: index = 0
    codetext = convert_to_string(code)
    return codetext

def phillips_decode(codetext,key,route=0,ptype='R'):
    """
    Input strings codetext and key, default route is horizontal.
    default type is ordinary Phillips ( not C or RC)    
    Output Phillips plaintext string.
    """
    code = convert_string(codetext,noJ=1)
    squares = setup_squares(key,route,ptype)
    period = 8
    index = 0
    count = 0
    plain = []
    for c in code:
        co = find_keysquare_coordinates(c,squares[index])
        if co[0] == -1 :
            print "Program Bug!"
            return "ERROR"
        d = squares[index][ (co[0]+4)%5][ (co[1]+4)%5]
        plain.append(d)
        count = count+1
        if count == 5:
            count = 0
            index = index+1
            if index == period: index = 0
    plaintext = convert_to_string(plain)
    return plaintext

#Fractionated Morse routines
morse_dict = { 'e':[0],
        't':[1],
        'i':[0,0],
        'a':[0,1],
        'n':[1,0],
        'm':[1,1],
        's':[0,0,0],
        'u':[0,0,1],
        'r':[0,1,0],
        'w':[0,1,1],
        'd':[1,0,0],
        'k':[1,0,1],
        'g':[1,1,0],
        'o':[1,1,1],
        'h':[0,0,0,0],
        'v':[0,0,0,1],
        'f':[0,0,1,0],
        'l':[0,1,0,0],
        'p':[0,1,1,0],
        'j':[0,1,1,1],
        'b':[1,0,0,0],
        'x':[1,0,0,1],
        'c':[1,0,1,0],
        'y':[1,0,1,1],
        'z':[1,1,0,0],
        'q':[1,1,0,1],
        '1':[0,1,1,1,1],
        '2':[0,0,1,1,1],
        '3':[0,0,0,1,1],
        '4':[0,0,0,0,1],
        '5':[0,0,0,0,0],
        '6':[1,0,0,0,0],
        '7':[1,1,0,0,0],
        '8':[1,1,1,0,0],
        '9':[1,1,1,1,0],
        '0':[1,1,1,1,1],
        '.':[0,1,0,1,0,1],
        ',':[1,1,0,0,1,1],
        '?':[0,0,1,1,0,0],
        ':':[1,1,1,0,0,0],
        ';':[1,0,1,0,1,0],
        '-':[1,0,0,0,0,1],
        '/':[1,0,0,1,0],
        '=':[1,0,0,0,1],
        '@':[0,1,1,0,1,0],
        '"':[0,1,0,0,1,0],
        "'":[0,1,1,1,1,0]
}

morse_reverse_dict = {(1, 1, 0, 0) :'z',
    (1, 0, 0, 1) :'x',
    (1, 0, 1, 1) :'y',
    (0, 0, 0, 1) :'v',
    (0, 1, 1) :'w',
    (1,) :'t',
    (0, 0, 1) :'u',
    (0, 1, 0) :'r',
    (0, 0, 0) :'s',
    (0, 1, 1, 0) :'p',
    (1, 1, 0, 1) :'q',
    (1, 0) :'n',
    (1, 1, 1) :'o',
    (0, 1, 0, 0) :'l',
    (1, 1) :'m',
    (0, 1, 1, 1) :'j',
    (1, 0, 1) :'k',
    (0, 0, 0, 0) :'h',
    (0, 0) :'i',
    (0, 0, 1, 0) :'f',
    (1, 1, 0) :'g',
    (1, 0, 0) :'d',
    (0,) :'e',
    (1, 0, 0, 0) :'b',
    (1, 0, 1, 0) :'c',
    (0, 1) :'a',
    (0, 1, 0, 1, 0, 1) :'?',
    (1, 0, 0, 0, 1) :'=',
    (1, 1, 1, 0, 0, 0) :':',
    (1, 0, 1, 0, 1, 0) :';',
    (1, 1, 1, 0, 0) :'8',
    (1, 1, 1, 1, 0) :'9',
    (1, 0, 0, 0, 0) :'6',
    (1, 1, 0, 0, 0) :'7',
    (0, 0, 0, 0, 1) :'4',
    (0, 0, 0, 0, 0) :'5',
    (0, 0, 1, 1, 1) :'2',
    (0, 0, 0, 1, 1) :'3',
    (1, 1, 1, 1, 1) :'0',
    (0, 1, 1, 1, 1) :'1',
    (0,1,0,1,0,1):'.',
    (1,1,0,0,1,1):',',
    (0,0,1,1,0,0):'?',
    (1,1,1,0,0,0):':',
    (1,0,1,0,1,0):';',
    (1,0,0,0,0,1):'-',
    (1,0,0,1,0):'/',
    (1,0,0,0,1):'=',
    (0,1,1,0,1,0):'@',
    (0,1,0,0,1,0):'"',
    (0,1,1,1,1,0):"'"
}


def fractionated_morse_encode(plaintext,key):
    """
    Input strings plaintext and key and output unformated
    fractionated morse codetext
    """
    # codes: 0 = dot, 1 = dash ,2 = end of letter
    END_SYMBOL = 2
    #make up 256 value string "trans" that translates upper case to lower and all non-letters to blanks
    #but maybe include digits
    #appengine doesn't like trans routine, change to more orthodox one
#     i_r = map(chr, range(256))
#     trans = [' '] * 256
#     o_a, o_z = ord('a'), (ord('z')+1)
#     trans[ord('A'):(ord('Z')+1)] = i_r[o_a:o_z]
#     trans[o_a:o_z] = i_r[o_a:o_z]
#     trans[ord('0'):(ord('9')+1)] = i_r[ord('0'):(ord('9')+1)]
#     trans = ''.join(trans)
#     plain = plaintext.translate(trans)
    plaintext1 = plaintext.lower()
    ok = 'abcdefghijklmnopqrstuvwxyz0123456789'
    plain = ''
    for c in plaintext1:
        if c in ok:
            plain += c
        else:
            plain += ' '
    plain = plain.split()
    mcode = []
    for wrd in plain:
        for c in wrd:
            mcode += morse_dict[c]
            mcode.append(END_SYMBOL)
        mcode.append(END_SYMBOL)
    #mcode ends in two END_SYMBOLS, if mcode not multiple of 3 remove some.
    n = len(mcode) % 3
    if n == 1:
        mcode = mcode[ :-1]
    elif n == 2 :
        mcode = mcode[ :-2]
    keyarray = get_key_array(key,'')
    code = []
    for i in range(0,len(mcode),3):
        c1 = mcode[i]
        c2 = mcode[i+1]
        c3 = mcode[i+2]
        index = 9*c1+3*c2+c3
        code.append( keyarray[index] )
    codetext = convert_to_string(code)
    return [codetext,mcode]

def fractionated_morse_decode(codetext,key):
    """
    Input strings codetext and key, output plaintext string
    """
    END_SYMBOL = 2
    code = convert_string(codetext)
    keyarray = get_key_array(key,'')
    mcode = []
    for c in code:
        n = keyarray.index(c)
        c1 = int(n/9)
        c2 = int ( (n%9)/3 )
        c3 = n % 3
        mcode += [c1,c2,c3]
    if mcode[-1] != END_SYMBOL : mcode.append(END_SYMBOL)
    plain = []
    ltr = ()
    for d in mcode:
        if d == END_SYMBOL:
            if ltr == (): plain.append(' ')
            else:
                if ltr not in morse_reverse_dict.keys():
                    return ["ERROR! code has sequence with no morse translation",mcode]
                plain.append( morse_reverse_dict[ltr])
                ltr = ()
        else :
            ltr = ltr+(d,)
    plaintext = ''.join(plain)
    return [plaintext,mcode]

def morbit_encode(plaintext,key):
    """
    input strings plaintext and key. Output
    morbit encoded string of digits
    """
    END_SYMBOL = 2
#     #make up 256 value string "trans" that translates upper case to lower and all non-letters to blanks
#     #but maybe include digits
#     i_r = map(chr, range(256))
#     trans = [' '] * 256
#     o_a, o_z = ord('a'), (ord('z')+1)
#     trans[ord('A'):(ord('Z')+1)] = i_r[o_a:o_z]
#     trans[o_a:o_z] = i_r[o_a:o_z]
#     trans[ord('0'):(ord('9')+1)] = i_r[ord('0'):(ord('9')+1)]
#     trans = ''.join(trans)
#     plain = plaintext.translate(trans)
    plaintext1 = plaintext.lower()
    ok = 'abcdefghijklmnopqrstuvwxyz0123456789'
    plain = ''
    for c in plaintext1:
        if c in ok:
            plain += c
        else:
            plain += ' '
    plain = plain.split()
    mcode = []
    for wrd in plain:
        for c in wrd:
            mcode += morse_dict[c]
            mcode.append(END_SYMBOL)
        mcode.append(END_SYMBOL)
    #mcode ends in two END_SYMBOLS, if mcode not multiple of 2 remove one
    if len(mcode) & 1 : mcode = mcode[ :-1]
    offset = get_hat_offset(key)
    nkey = offset_to_key(offset)
    if len(nkey) != 9 :
        print "Key does not have length 9!"
        return "ERROR"
    code = []
    for i in range(0,len(mcode),2):
        c1 = mcode[i]
        c2 = mcode[i+1]
        index = 3*c1+c2
        code.append( nkey[index] )
    codetext = ""
    for n in code:
        codetext += chr(n+ord('1'))
    return [codetext,mcode]

def morbit_decode(codetext,key):
    """
    input strings code text and key.
    output morbit decoded plaintext string.
    """
    END_SYMBOL = 2
    code = convert_numb_string(codetext)
    offset = get_hat_offset(key)
    nkey = offset_to_key(offset)
    if len(nkey) != 9 :
        print "Key does not have length 9!"
        return "ERROR"
    mcode = []
    for c in code:
        n = nkey.index(c-1)
        c1 = int(n/3)
        c2 = n % 3
        mcode += [c1,c2]
    if mcode[-1] != END_SYMBOL : mcode.append(END_SYMBOL)
    plain = []
    ltr = ()
    for d in mcode:
        if d == END_SYMBOL:
            if ltr == (): plain.append(' ')
            else:
                if ltr not in morse_reverse_dict.keys():
                    return ["ERROR! code has sequence with no morse translation",mcode]
                plain.append( morse_reverse_dict[ltr])
                ltr = ()
        else :
            ltr = ltr+(d,)
    plaintext = ''.join(plain)
    return [plaintext,mcode]

def pollux_encode(plaintext,key):
    """
    input strings plaintext and key. key consists of ordered string of
    10 entries, each entry is '.','-',or 'x'.
    output codetext string.
    """
    END_SYMBOL = 2
    #make up 256 value string "trans" that translates upper case to lower and all non-letters to blanks
    #but maybe include digits
#     i_r = map(chr, range(256))
#     trans = [' '] * 256
#     o_a, o_z = ord('a'), (ord('z')+1)
#     trans[ord('A'):(ord('Z')+1)] = i_r[o_a:o_z]
#     trans[o_a:o_z] = i_r[o_a:o_z]
#     trans[ord('0'):(ord('9')+1)] = i_r[ord('0'):(ord('9')+1)]
#     trans = ''.join(trans)
#     plain = plaintext.translate(trans)
    plaintext1 = plaintext.lower()
    ok = 'abcdefghijklmnopqrstuvwxyz0123456789'
    plain = ''
    for c in plaintext1:
        if c in ok:
            plain += c
        else:
            plain += ' '
    plain = plain.split()
    mcode = []
    for wrd in plain:
        for c in wrd:
            mcode += morse_dict[c]
            mcode.append(END_SYMBOL)
        mcode.append(END_SYMBOL)
    keyarray = [0]*10
    index = 1
    for c in key:
        if c == '.' :
            keyarray[ index ] = 0
        elif c == '-' or c == '_':
            keyarray[ index ] = 1
        elif c == 'x' or c =='X':
            keyarray[ index ] = END_SYMBOL
        index = (index+1)%10
    inverse_key = [None]*3
    for i in range(3):
        inverse_key[i] = []
    for i in range(10):
        inverse_key[ keyarray[i] ].append(i)
    code = []
    for c in mcode:
        n = randrange( len(inverse_key[c]))
        code.append( inverse_key[c][n] )
    codetext = ""
    for c in code:
        codetext += chr( c+ord('0') )
    return [codetext,mcode]

def pollux_decode(codetext,key):
    """
    input strings codetext and key. key consists of ordered string of
    10 entries, each entry is '.','-',or 'x'.
    output plaintext string.
    """
    END_SYMBOL = 2
    code = convert_numb_string(codetext)
    keyarray = [0]*10
    index = 1
    for c in key:
        if c == '.' :
            keyarray[ index ] = 0
        elif c == '-' or c == '_':
            keyarray[ index ] = 1
        elif c == 'x' or c =='X':
            keyarray[ index ] = END_SYMBOL
        index = (index+1)%10
    mcode = [keyarray[c] for c in code ]
    if mcode[-1] != END_SYMBOL : mcode.append(END_SYMBOL)
    plain = []
    ltr = ()
    for d in mcode:
        if d == END_SYMBOL:
            if ltr == (): plain.append(' ')
            else:
                if ltr not in morse_reverse_dict.keys():
                    return ["ERROR! code has sequence with no morse translation",mcode]
                plain.append( morse_reverse_dict[ltr])
                ltr = ()
        else :
            ltr = ltr+(d,)
    plaintext = ''.join(plain)
    return [plaintext,mcode]

#Ragbaby routines
def ragbaby_encode(plaintext,key):
    """
    Input strings plaintext and key. Encode
    with ragbaby cipher. Output upper case
    codetext with word divisions.
    """
    #get 24 letter keyed alphabet
    key_code = get_key_array(key,'jx')
    key_alphabet = convert_to_string(key_code)
    plain = plaintext.lower()
    plain = plain.replace('j','i')
    plain = plain.replace('x','w')      
    ok = 'abcdefghijklmnopqrstuvwxyz'
    special = "-'=" #characters that may occur in middle of words
    code = ''
    start_pos = 0
    word_flag = 0
    le = len(plain)
    for n in range(le):
        c = plain[n]
        if c in ok:
            if word_flag == 0:
                start_pos = (start_pos+1)%24
                index = start_pos
                word_flag = 1
            i = key_alphabet.index(c)
            code += key_alphabet[ (i+index)%24 ]
            index +=1
        else:
            word_flag = 0
            code += c
            if c in special and n>0 and n<le-1 :
                if plain[n-1] in ok and plain[n+1] in ok: # in middle of hyphenated or apostrophed word
                    word_flag = 1
    return code.upper()
    
def ragbaby_decode(codetext,key):
    """
    Input strings codetext and key. Decode
    with ragbaby cipher. Output lower case
    plaintext with word divisions.
    """
    #get 24 letter keyed alphabet
    key_code = get_key_array(key,'jx')
    key_alphabet = convert_to_string(key_code)
    code = codetext.lower()
    code = code.replace('j','i')
    code = code.replace('x','w')      
    ok = 'abcdefghijklmnopqrstuvwxyz'
    special = "-'=" #characters that may occur in middle of words
    plain = ''
    start_pos = 0
    word_flag = 0
    le = len(code)
    for n in range(le):
        c = code[n]
        if c in ok:
            if word_flag == 0:
                start_pos = (start_pos+1)%24
                index = start_pos
                word_flag = 1
            i = key_alphabet.index(c)
            plain += key_alphabet[ (24+i-index)%24 ]
            index +=1
        else:
            word_flag = 0
            plain += c
            if c in special and n>0 and n<le-1 :            
                if code[n-1] in ok and code[n+1] in ok: # in middle of hyphenated or apostrophed word
                    word_flag = 1
    return plain


#Portax routines
def get_portax_pair(cl,cr,kl):
    """
    return portax pair corresponding to digit pair cl,cr with key digit kl
    """
    k = kl/2
    if cl < 13 : t_flag = 0
    else: t_flag = 2
    if (cr % 2) > 0 : b_flag = 1
    else: b_flag = 0
    sum = t_flag + b_flag
    top_index = (cl+k)%13
    bot_index = (13+(cr>>1)-k)%13
    if sum is 0: #both top rows
        if bot_index == cl: #vertically aligned
            result = [ top_index+13,cr+1]
        else:
            result = [ bot_index, 2*top_index]
    elif sum is 1: #cl top, cr bottom
        if bot_index == cl:
            result = [ top_index+13, cr-1]
        else:
            result = [ bot_index, 2*top_index+1]
    elif sum is 2: #cl bottom, cr top
        if cl-13 <> (cr >> 1) : # cl,cr not verticaly aligned
            result = [ (cr >> 1)+13, (cl-13) << 1]
        else:
            result = [ (cl-k)%13, cr+1]
    else: # cl,cr both bottom
        if cl-13 <> (cr>>1) : # cl, cr not vertically aligned
            result = [(cr>>1)+13,( (cl-13)<<1 )+1 ]
        else:
            result = [ (cl-k)%13, cr-1]
    return result

def portax_decode_encode(codetext,key):
    """
    input strings codetext and key. Output portax
    plaintext string. Also works in reverse.
    """
    code = convert_string(codetext)
    if len(code) & 1:
        print "Odd number of letters!"
        return "ERROR"
    key_code = convert_string(key)
    keyl = len(key_code)
    plain = [None]*len(code)
    for i in range(0,len(code),2*keyl):
        for index in range( keyl):
            if i+index+keyl >= len(code): break
            cl = code[i+index]
            cr = code[i+index+keyl]
            result = get_portax_pair(cl,cr,key_code[index])
            plain[i+index] = result[0]
            plain[i+index+keyl] = result[1]
    remainder = len(code) % (2*keyl)
    if remainder:
        n = len(code) - remainder
        for index in range(remainder/2):
            cl = code[n+index]
            cr = code[n+index+remainder/2]
            result = get_portax_pair(cl,cr,key_code[index])
            plain[n+index] = result[0]
            plain[n+index+remainder/2] = result[1]
    plaintext = convert_to_string(plain)
    return plaintext

#checkerboard routines
def checkerboard_encode(plaintext,vertical_key,horizontal_key,key,route=0,use6x6=0):
    """
    input strings plaintext and keys. Default route is horizontal.
    vertical_key can have 5 or 10 letters (or 6 or 12), as can horizontal_key.
    The other key is the keysquare key.
    Output checkerboard-encrypted codetext string.
    """
    vkey = convert_string(vertical_key,use6x6=use6x6)
    if use6x6:
        le = 6
        numb_sym = 36
    else:
        le = 5
        numb_sym = 26
    v2 = len(vkey) - le #should be le or 0
    if v2 <> 0 and v2 <> le :
        print "Error in vertical key"
        return "ERROR"
    used_let = [-1]*numb_sym
    for i in range(len(vkey)):
        c = vkey[i]
        if used_let[c] <> -1 and (i%le) != used_let[c]:
            print "Same letter in different vertical positions!"
            return "ERROR"
        used_let[c] = i
    hkey = convert_string(horizontal_key,use6x6=use6x6)
    h2 = len(hkey) - le #should be le or 0
    if h2 <> 0 and h2 <> le :
        print "Error in horizontal key"
        return "ERROR"
    used_let = [-1]*numb_sym
    for i in range(len(hkey)):
        c = hkey[i]
        if used_let[c] <> -1 and (i%le) != used_let[c]:
            print "Same letter in different horizontal positions!"
            return "ERROR"
        used_let[c] = i
    ksquare = get_keysquare(key,route = route,use6x6=use6x6)
    plain = convert_string(plaintext,use6x6=use6x6)
    code = []
    for c in plain:
        co = find_keysquare_coordinates(c,ksquare,use6x6=use6x6)
        y = v2 * randrange(2)
        x = h2 * randrange(2)
        code.append( vkey[co[0]+y])
        code.append( hkey[co[1]+x])
    codetext = convert_to_string(code)
    return [codetext,convert_to_string(vkey,use6x6=use6x6),convert_to_string(hkey,use6x6=use6x6)]

def checkerboard_decode(codetext,vertical_key,horizontal_key,key,route=0,use6x6=0):
    """
    input strings codetext and keys. Default route is horizontal.
    vertical_key can have 5 or 10 (or 6 or 12) letters, as can horizontal_key.
    The other key is the keysquare key.
    Output checkerboard-decrypted plaintext string.
    """
    vkey = convert_string(vertical_key,use6x6=use6x6)
    if use6x6:
        le = 6
        numb_sym = 36
    else:
        le = 5
        numb_sym = 26
    v2 = len(vkey) - le #should be le or 0
    if v2 <> 0 and v2 <> le :
        print "Error in vertical key"
        return "ERROR"
    used_let = [-1]*numb_sym
    for i in range(len(vkey)):
        c = vkey[i]
        if used_let[c] <> -1 and (i%le) != used_let[c]:
            print "Same letter in different vertical positions!"
            return "ERROR"
        used_let[c] = i
    hkey = convert_string(horizontal_key,use6x6=use6x6)
    h2 = len(hkey) - le #should be le or 0
    if h2 <> 0 and h2 <> le :
        print "Error in horizontal key"
        return "ERROR"
    used_let = [-1]*numb_sym
    for i in range(len(hkey)):
        c = hkey[i]
        if used_let[c] <> -1 and (i%le) != used_let[c]:
            print "Same letter in different horizontal positions!"
            return "ERROR"
        used_let[c] = i
    ksquare = get_keysquare(key,route = route,use6x6=use6x6)
    code = convert_string(codetext,use6x6=use6x6)
    if len(code) & 1:
        print "Odd number of codetext characters!"
        return "ERROR"
    plain = []
    state = 0
    for c in code:
        if state :
            x = hkey.index(c) % le
            plain.append( ksquare[y][x] )
            state = 0
        else :
            y = vkey.index(c) % le
            state = 1
    plaintext = convert_to_string(plain,use6x6=use6x6)
    return [plaintext,convert_to_string(vkey,use6x6=use6x6),convert_to_string(hkey,use6x6=use6x6)]

#Bazeries routines
def xlate_baz(numb):
    """
    translate list 'numb' and return corresponding english text string
    """
    word1 = ['one','two','three','four','five','six','seven','eight','nine']
    word2 = ['eleven','twelve','thirteen','fourteen','fifteen','sixteen',\
         'seventeen','eighteen','nineteen']
    word3 = ['twenty','thirty','forty','fifty','sixty','seventy','eighty','ninety']
    to_go = len(numb)
    index = 0
    text = ""
    while to_go > 0:
        if to_go is 6:
            text += word1[ numb[index]-1]+"hundred"
            index += 1
            to_go -= 1
        elif to_go is 5:
            if numb[index] == 1:
                text += word2[ numb[index+1]-1]+"thousand"
                index += 2
                to_go -= 2
            else:
                text += word3[ numb[index]-2]
                index += 1
                to_go -= 1
        elif to_go is 4:
            text += word1[ numb[index] -1 ]+ "thousand"
            index += 1
            to_go -= 1
        elif to_go is 3:
            text += word1[ numb[index] -1 ]+ "hundred"
            index += 1
            to_go -= 1
        elif to_go is 2:
            if numb[index] == 1:
                text += word2[ numb[index+1]-1]
                index += 2
                to_go -= 2
            else:
                text += word3[ numb[index]-2]
                index += 1
                to_go -= 1
        elif to_go is 1:
            text += word1[ numb[index] -1 ]
            to_go -= 1
    return text

def bazeries_encode(plaintext,key,route = 0,alpha_key=''):
    """
    input strings plaintext and key. Default route is horizontal.
    output bazeries encoded ciphertext string.
    """
    key_num = convert_numb_string(key)
    if alpha_key == '':
        key_word = xlate_baz(key_num)
    else:
        key_word = alpha_key
    left_square = get_keysquare('A',3) # 3 is vertical route
    right_square = get_keysquare(key_word,route = route)
    plain = convert_string(plaintext,noJ=1)
    index = pos = 0
    code = []
    while pos < len(plain):
        n = key_num[index]
        pt = plain[pos:pos+n]
        pt.reverse()
        for c in pt:
            co = find_keysquare_coordinates(c,left_square)
            code.append( right_square[ co[0] ][ co[1] ] )
        index = (index+1) % len(key_num)
        pos += n
    codetext = convert_to_string(code)
    return [codetext,right_square]

def bazeries_6x6_encode(plaintext,key,route = 0,alpha_key=''):
    """
    input strings plaintext and key. Default route is horizontal.
    output 6x6 bazeries encoded ciphertext string.
    """
    alpha1="a1b2c3d4e5f6g7h8i9j0klmnopqrstuvwxyz"   
    key_num = convert_numb_string(key)
    if alpha_key == '':
        key_word = xlate_baz(key_num)
    else:
        key_word = alpha_key
    right_square = get_6x6_keysquare(key_word,route = route)    
    plaintext = plaintext.lower()
    plain = [c for c in plaintext if c in alpha1]
    index = pos = 0
    code = []
    while pos < len(plain):
        n = key_num[index]
        pt = plain[pos:pos+n]
        pt.reverse()
        for c in pt:
            c_row = alpha1.index(c)/6
            c_col = alpha1.index(c) % 6
            #c_index = 6*c_col+c_row #plain keysquare is vertical
            #code.append( key[c_index] )
            code.append(right_square[c_col][c_row])
        index = (index+1) % len(key_num)
        pos += n
    codetext = convert_to_6x6_string(code)    
    return [codetext,right_square]    
    
    
def bazeries_decode(codetext,key,route = 0,alpha_key = ''):
    """
    input strings codetext and key. Default route is horizontal.
    outpu bazeries encoded ciphertext string.
    """
    key_num = convert_numb_string(key)
    if alpha_key == '':
        key_word = xlate_baz(key_num)
    else:
        key_word = alpha_key
    left_square = get_keysquare('A',3) # 3 is vertical route
    right_square = get_keysquare(key_word,route = route)
    code = convert_string(codetext)
    index = pos = 0
    plain = []
    while pos < len(code):
        n = key_num[index]
        pt = code[pos:pos+n]
        pt.reverse()
        for c in pt:
            co = find_keysquare_coordinates(c,right_square)
            plain.append( left_square[ co[0] ][ co[1] ] )
        index = (index+1) % len(key_num)
        pos += n
    plaintext = convert_to_string(plain)
    return [plaintext,right_square]

def bazeries_6x6_decode(codetext,key,route = 0,alpha_key = ''):
    """
    input strings codetext and key. Default route is horizontal.
    outpu 6x6 bazeries encoded ciphertext string.
    """
    alpha1="a1b2c3d4e5f6g7h8i9j0klmnopqrstuvwxyz"  
    key_num = convert_numb_string(key)
    if alpha_key == '':
        key_word = xlate_baz(key_num)
    else:
        key_word = alpha_key
    right_square = get_6x6_keysquare(key_word,route = route) 
    code = convert_6x6_string(codetext)    
    pt = []
    pos = index = 0
    while pos < len(code):
        pr = code[pos:pos+key_num[index]]
        pr.reverse()
        for c in pr:
            co = find_keysquare_coordinates(c,right_square,use6x6=1)        
            p_row = co[0]
            p_col = co[1]
            pl = p_col*6+p_row #plain keysquare is vertical
            pt.append(pl)
        pos += key_num[index]
        index = (index+1)%len(key_num)
    #print "Key ",n
    plain = [alpha1[c] for c in pt]
    plaintext = ''.join(plain)
    return [plaintext,right_square]    
    
#Nihilist Substitution routines
def nihilist_sub_encode(plaintext,sqkey,key,route=0):
    """
    Input strings plaintext, sqkey, key. Default route is
    horizontal. Output Nihilist substitution codetext string.
    """
    plain = convert_string(plaintext,noJ=1)
    keysquare = get_keysquare(sqkey,route)
    nkey = convert_string(key,noJ=1)
    period = len(nkey)
    addkey = []
    for c in nkey:
        co = find_keysquare_coordinates(c,keysquare)
        n = 10*(co[0]+1)+co[1]+1
        addkey.append(n)
    code = ""
    index = 0
    for c in plain:
        co = find_keysquare_coordinates(c,keysquare)
        n = 10*(co[0]+1)+co[1]+1
        n += addkey[index]
        n %= 100
        code += "%02d" % n
        index = (index+1) % period
    return [code,addkey]

def nihilist_sub_decode(codetext,sqkey,key,route=0):
    """
    Input strings codetext, sqkey, key. Default route is
    horizontal. Output Nihilist substitution plaintext string.
    """
    code = convert_numb_string(codetext)
    if len(code) & 1:
        #print "Odd number of digits!"
        return "ERROR: odd number of digits"
    keysquare = get_keysquare(sqkey,route)
    nkey = convert_string(key,noJ=1)
    period = len(nkey)
    addkey = []
    for c in nkey:
        co = find_keysquare_coordinates(c,keysquare)
        n = 10*(co[0]+1)+co[1]+1
        addkey.append(n)
    plain = []
    index = 0
    for i in range(0,len(code),2):
        n = 10*code[i]+code[i+1]
        if n < 11 : n += 100
        n -= addkey[index]
        c1 = int(n/10) -1
        c2 = (n%10) -1
        if c1 < 0 or c1 >4 or c2 < 0 or c2> 4:
            st = "ERROR! the number: "+str(10*code[i]+code[i+1])+" at position "+str(i+1)+" is outside keysquare"
            return [st,addkey]
        plain.append( keysquare[c1][c2] )
        index = (index+1) % period
    plaintext = convert_to_string(plain)
    return [plaintext,addkey]
    
def nihilist_sub_encode6x6(plaintext,sqkey,key,route=0):
    """
    Input strings plaintext, sqkey, key. Default route is
    horizontal. Output 6x6 Nihilist substitution codetext string.
    """
    plain = convert_string(plaintext,use6x6=1)
    keysquare = get_keysquare(sqkey,route,use6x6=1)
    nkey = convert_string(key,use6x6=1)
    period = len(nkey)
    addkey = []
    for c in nkey:
        co = find_keysquare_coordinates(c,keysquare,use6x6=1)
        n = 10*(co[0]+1)+co[1]+1
        addkey.append(n)
    code = ""
    index = 0
    for c in plain:
        co = find_keysquare_coordinates(c,keysquare,use6x6=1)
        n = 10*(co[0]+1)+co[1]+1
        n += addkey[index]
        n %= 100
        code += "%02d" % n
        index = (index+1) % period
    return [code,addkey]

def nihilist_sub_decode6x6(codetext,sqkey,key,route=0):
    """
    Input strings codetext, sqkey, key. Default route is
    horizontal. Output 6x6 Nihilist substitution plaintext string.
    """
    code = convert_numb_string(codetext)
    if len(code) & 1:
        #print "Odd number of digits!"
        return "ERROR: odd number of digits"
    keysquare = get_keysquare(sqkey,route,use6x6=1)
    nkey = convert_string(key,use6x6=1)
    period = len(nkey)
    addkey = []
    for c in nkey:
        co = find_keysquare_coordinates(c,keysquare,use6x6=1)
        n = 10*(co[0]+1)+co[1]+1
        addkey.append(n)
    plain = []
    index = 0
    for i in range(0,len(code),2):
        n = (100+10*code[i]+code[i+1] - addkey[index])%100
        c1 = int(n/10) -1
        c2 = (n%10) -1
        if c1 < 0 or c1 >5 or c2 < 0 or c2> 5:
            st = "ERROR! the number: "+str(10*code[i]+code[i+1])+" at position "+str(i+1)+" is outside keysquare"
            return [st,addkey]
        plain.append( keysquare[c1][c2] )
        index = (index+1) % period
    plaintext = convert_to_string(plain,use6x6=1)
    return [plaintext,addkey]
    
#Baconian routines
def baconian_encode(plaintext,key):
    """
    input strings plaintext and key. key is string of 26 entries a,b or 0,1.
    output baconian encoded codetext string
    """
    bacon_dict = { 'a':[0,0,0,0,0],'b':[0,0,0,0,1],'c':[0,0,0,1,0],'d':[0,0,0,1,1],'e':[0,0,1,0,0],\
    'f':[0,0,1,0,1],'g':[0,0,1,1,0],'h':[0,0,1,1,1],'i':[0,1,0,0,0],'j':[0,1,0,0,0],'k':[0,1,0,0,1],\
    'l':[0,1,0,1,0],'m':[0,1,0,1,1],'n':[0,1,1,0,0],'o':[0,1,1,0,1],'p':[0,1,1,1,0],'q':[0,1,1,1,1],\
    'r':[1,0,0,0,0],'s':[1,0,0,0,1],'t':[1,0,0,1,0],'u':[1,0,0,1,1],'v':[1,0,0,1,1],'w':[1,0,1,0,0],\
    'x':[1,0,1,0,1],'y':[1,0,1,1,0],'z':[1,0,1,1,1] }
    nkey = key.replace('a','0')
    nkey = nkey.replace('b','1')
    if len(nkey) <> 26:
        print "Key does not have 26 entries!"
        return "ERROR"
    inverse_key = [[],[]]
    for i in range(26):
        if nkey[i] == '0':
            inverse_key[0].append(i)
        else:
            inverse_key[1].append(i)
    plain= convert_string(plaintext)
    plain = convert_to_string(plain)
    code = []
    for c in plain.lower():
        v = bacon_dict[c]
        for d in v:
            n = randrange(len(inverse_key[d]))
            code.append( inverse_key[d][n])
    codetext = convert_to_string(code)
    return codetext

def baconian_decode(codetext,key):
    """
    input strings codetext and key. key is string of 26 entries a,b or 0,1.
    output baconian decoded plaintext string
    """
    bacon_reverse_dict = {\
    (1, 0, 1, 1, 1) :'z',\
    (1, 0, 1, 0, 1) :'x',\
    (1, 0, 1, 1, 0) :'y',\
    (1, 0, 1, 0, 0) :'w',\
    (1, 0, 0, 1, 0) :'t',\
    (1, 0, 0, 1, 1) :'u',\
    (1, 0, 0, 0, 0) :'r',\
    (1, 0, 0, 0, 1) :'s',\
    (0, 1, 1, 1, 0) :'p',\
    (0, 1, 1, 1, 1) :'q',\
    (0, 1, 1, 0, 0) :'n',\
    (0, 1, 1, 0, 1) :'o',\
    (0, 1, 0, 1, 0) :'l',\
    (0, 1, 0, 1, 1) :'m',\
    (0, 1, 0, 0, 1) :'k',\
    (0, 0, 1, 1, 1) :'h',\
    (0, 1, 0, 0, 0) :'i',\
    (0, 0, 1, 0, 1) :'f',\
    (0, 0, 1, 1, 0) :'g',\
    (0, 0, 0, 1, 1) :'d',\
    (0, 0, 1, 0, 0) :'e',\
    (0, 0, 0, 0, 1) :'b',\
    (0, 0, 0, 1, 0) :'c',\
    (0, 0, 0, 0, 0) :'a' }
    nkey = key.replace('a','0')
    nkey = nkey.replace('b','1')
    if len(nkey) <> 26:
        print "Key does not have 26 entries!"
        return "ERROR"
    code = convert_string(codetext)
    plain = []
    for i in range(0,len(code),5):
        lst = ()
        for j in range(i,i+5):
            lst +=( int(nkey[code[j]]),)
        plain.append( bacon_reverse_dict[lst])
    plaintext = "".join(plain)
    return plaintext

#Grandpre routines
def grandpre_encode(plaintext,key):
    """
    input string 'plaintext' and list of strings 'key'. output
    grandpre encoded codetext.
    """
    plain = convert_string(plaintext)
    nkey = [None]*len(key)
    if len(key) == 10:
        shift = 0
    else:
        shift = 1
    for i in range(len(key)):
        nkey[i] = convert_string(key[i])
    inverse_key = [None]*26
    for i in range(26):
        inverse_key[i] = []
    for n in range(26):
        for i in range(len(key)):
            for j in range(len(key)):
                if n == nkey[i][j]:
                    s = "%02d"%( 10*((i+shift )%10)+((j+shift)%10) )
                    inverse_key[n].append(s )
    code = []
    for c in plain:
        n = randrange( len(inverse_key[c]) )
        code.append( inverse_key[c][n] )
    codetext = "".join(code)
    return codetext

def grandpre_decode(codetext,key):
    """
    input string codetext and list of strings 'key'. Output
    grandpre decodetext plaintext string.
    """
    code = convert_numb_string(codetext)
    if len(code) & 1:
        print "Odd numbers of digits!"
        return "ERROR"
    nkey = [None]*len(key)
    if len(key) == 10:
        shift = 0
    else:
        shift = 1
    for i in range(len(key)):
        nkey[i] = convert_string(key[i])
    plain = []
    for i in range(0,len(code),2):
        plain.append( nkey[ code[i]-shift ][ code[i+1]-shift ])
    plaintext = convert_to_string(plain)
    return plaintext

#Monome_dinome routines
def monome_dinome_encode(plaintext,columns,rows,key,letter_in,letter_out):
    """
    input strings plaintext, columns (8 digits giving column order),
    rows (2 digits giving rows order), and key. Output monome-dinome
    encoded codetext string.
    """
    #change to 24 letter alphabet
    plain = plaintext.lower()
    plain = plain.replace('j','i')
    plain = plain.replace(letter_in,letter_out)
    plain = convert_string(plain)
    s='j'+letter_in
    key_code = get_key_array(key,s)
    code = []
    for c in plain:
        x = key_code.index(c)
        row = int(x/8)
        if row == 0:
            code.append(columns[x])
        elif row == 1:
            code.append( rows[0]+columns[ x%8] )
        else:
            code.append( rows[1]+columns[ x % 8])
    codetext = ''.join(code)
    return codetext

def monome_dinome_decode(codetext,columns,rows,key,letter_in):
    """
    input strings codetext, columns (8 digits giving column order),
    rows (2 digits giving rows order), and key. Output monome-dinome
    decoded plaintext string.
    """
    code = convert_numb_string(codetext)
    column_key = convert_numb_string(columns)
    row_key = convert_numb_string(rows)
    #use 24 letter alphabet
    s = 'j'+letter_in
    key_code = get_key_array(key,s) #sometimes 'jz'
    plain = []
    row = 0
    for c in code:
        if row == 2:
            n = column_key.index(c)
            plain.append(key_code[ n+16] )
            row = 0
        elif row == 1:
            n = column_key.index(c)
            plain.append(key_code[ n+8] )
            row = 0
        elif c == row_key[0]: row = 1
        elif c == row_key[1]: row = 2
        else:
            n = column_key.index(c)
            plain.append( key_code[n] )
    plaintext = convert_to_string(plain)
    return plaintext

#Headline routines
def headline_encode(headlines,hat,key,setting):
    """
    input 'headlines' a list of 5 headline strings, and strings
    hat,key,setting. Output encoded list of headline strings
    """
    key_code = get_key_array(key,'')
    key_array = convert_to_string(key_code)
    tramp_key = columnar_encode(key_array,hat)[0]
    quag_key = get_quagmire_array(tramp_key,tramp_key,setting,tramp_key[0])
    alphabet = 'abcdefghijklmnopqrstuvwxyz'
    codes = [None]*5
    for n in range(5):
        codes[n] = ""
        for c in headlines[n].lower():
            d = c
            if c in alphabet:
                j = ord(c)-ord('a')
                x = quag_key[5].index(j)
                y = quag_key[n][x]
                d = chr(y+ord('A'))
            codes[n] += d
    return codes

def headline_decode(headlines,hat,key,setting):
    """
    input 'headlines' a list of 5 encoded headline strings, and strings
    hat,key,setting. Output decoded list of headline strings
    """
    key_code = get_key_array(key,'')
    key_array = convert_to_string(key_code)
    tramp_key = columnar_encode(key_array,hat)[0]
    quag_key = get_quagmire_array(tramp_key,tramp_key,setting,tramp_key[0])
    alphabet = 'abcdefghijklmnopqrstuvwxyz'
    plainlines = [None]*5
    for n in range(5):
        plainlines[n] = ""
        for c in headlines[n].lower():
            d = c
            if c in alphabet:
                j = ord(c)-ord('a')
                x = quag_key[n].index(j)
                y = quag_key[5][x]
                d = chr(y+ord('a'))
            plainlines[n] += d
    return plainlines

#tridigital routine, encode only, decode would be ambiguous
def tridigital_encode(plaintext,hat,key):
    """
    Input strings plaintext, hat and key. Hat must have 10 letters. Output
    tridigital code string.
    """
    #make up 256 value string "trans" that translates upper case to lower and all non-letters to blanks
    i_r = map(chr, range(256))
    trans = [' '] * 256
    o_a, o_z = ord('a'), (ord('z')+1)
    trans[ord('A'):(ord('Z')+1)] = i_r[o_a:o_z]
    trans[o_a:o_z] = i_r[o_a:o_z]
    trans = ''.join(trans)
    plain = plaintext.translate(trans)
    plain = plain.split()
    offset = get_hat_offset(hat)
    nhat = offset_to_key(offset)
    if len(nhat) != 10 :
        print "Hat does not have length 10!"
        return "ERROR"
    usehat = [ (i+1) %10 for i in nhat]
    array = get_key_array(key,'')
    numb_array = [None]*26
    index = 0
    for c in array:
        numb_array[c] = usehat[index]
        index = (index+1)%9
    end_of_word = "%d" % usehat[9]
    code = []
    for wrd in plain:
        for c in wrd:
            code.append( "%d" % numb_array[ord(c)-ord('a')] )
        code.append(end_of_word)
    code = code[ :-1] #dump end_of_word digit at end
    return ''.join(code)

# Cipher ID routines
def get_ic(code):
    """
    get index of coincidence of a list of code digits
    """
    sum = 0.0
    for i in range(26):
        sum += code.count(i)*(code.count(i)-1)
    ic = sum / (len(code)*(len(code)-1))
    return ic

def get_dic(code):
    """
    get 10,000 x digraphic index of coincidence of code digits
    """
    def get_index(x,y): return x+26*y
    list = map(get_index,code[ :-1],code[1: ])
    le = len(list)
    sum = 0.0
    for i in range(26*26):
        sum += list.count(i)*(list.count(i)-1)
    dic = 10000.00 * sum / (le*(le-1))
    return dic

def get_LR(code):
    """
    get LR stat for a list of code digits
    """
    reps = [0]*11
    for i in range(len(code)):
     for j in range(i+1,len(code)):
        n  = 0
        while j+n < len(code) and code[i+n] == code[j+n]:
            n += 1
        if n > 10: n = 10
        reps[n] += 1

    return 1000*sqrt(reps[3])/len(code)

def get_ROD(code):
    """
    get ROD stat for a list of code digits
    """
    sum_all = sum_odd = 0
    for i in range(len(code)):
     for j in range(i+1,len(code)):
        n  = 0
        while j+n < len(code) and code[i+n] == code[j+n]:
            n += 1
        if n > 1:
            sum_all += 1
            if (j-i) & 1 :
                sum_odd += 1
    if sum_all == 0:
        return 50.0
    return 100.0 * sum_odd / sum_all


def get_odd_even_dic(code):
    """
    get 10,000 x digraphic index of coincidence of code digits
    for pairs starting at odd and even locations
    """
    def get_index(x,y): return x+26*y
    list = map(get_index,code[ :-1],code[1: ])
    le = len(list)
    even_freq = [0]*(26*26)
    even_count = 0
    odd_freq = [0]*(26*26)
    odd_count = 0
    # could use list.count instead in next line
    state = 1
    for x in list:
        if state:
            even_freq[x] +=1
            even_count += 1
        else:
            odd_freq[x] += 1
            odd_count += 1
        state ^= 1
    sum = 0.0
    for i in range(26*26):
        sum += even_freq[i]*(even_freq[i]-1)
    even_dic = 10000.00 * sum / (even_count*(even_count-1))
    sum = 0.0
    for i in range(26*26):
        sum += odd_freq[i]*(odd_freq[i]-1)
    odd_dic = 10000.00 * sum / (odd_count*(odd_count-1))
    return odd_dic,even_dic

def get_sorted_freqs(code):
    """
    return sorted list of letter freqencies from list of code digits
    """
    freq = [(code.count(x),chr(x+ord('A'))) for x in range(26)]
    freq.sort()
    freq.reverse()
    return [ (l,c) for (c,l) in freq ]

def periodic_ic(code,max_period):
    """
    given list of code digits, return average IC of all periods from 1 to max_period
    """
    ic = [0.0]
    for period in range(1,max_period+1):
            freq = [None]*period
            for j in range(period):
                    freq[j] = [0]*26
            index = 0
            for c in code:
                    freq[index][c] += 1
                    index = (index+1)%period
            z = 0.0
            for i in range(period):
                    x = 0.0
                    y = 0.0
                    for j in range(26):
                            x += freq[i][j]*(freq[i][j]-1)
                            y += freq[i][j]
                    z += x/(y*(y-1))
            z = z/period
            ic.append(z)
    return ic

def nicodemus_ic(code,max_period):
    """
    given list of code digits, return Nicodemus IC of all periods from 1 to max_period
    """
    ic = [0.0]
    for period in range(1,max_period+1):
            freq = [None]*period
            for j in range(period):
                    freq[j] = [0]*26
            index = 0
    #round off to multiple of period*5
    block = int(len(code)/ (5*period))
    limit = block*5*period
    for i in range(limit):
        freq[index][code[i]] += 1
        if ((i+1)% 5)==0:
            index = (index+1)%period
    z = 0.0
    for i in range(period):
             x = 0.0
             y = 0.0
             for j in range(26):
                   x += freq[i][j]*(freq[i][j]-1)
                   y += freq[i][j]
    z += x/(y*(y-1))
    z = z/period
    ic.append(z)
    return ic

def get_numb_doubled_pairs(code):
    """
    return number of doubled even numbered pairs
    """
    numb = 0
    for i in range(0,len(code)-1,2):
        if code[i] == code[i+1]:
            numb += 1
    return numb

def seriated_period(code,period):
    """
    input coded digits and period, return two-element list whose first entry is
    number of doubled pairs for that period, and whose second entry is zero
    if there are doubled pairs and the even DIC if there are no doubled pairs
    """
    le = len(code)
    if le & 1 : return [1,0.0] #odd number of letters
    left_over = le % (2*period)
    #construct new letter grouping
    index = pos = 0
    nlist = [0]*le
    while pos < le - left_over:
        for i in range(period):
            nlist[index] = code[pos+i]
            nlist[index+1] = code[pos+period+i]
            index += 2
        pos += 2*period
    if left_over:
        pos = le - left_over
        for i in range(left_over/2):
            nlist[index] = code[pos+i]
            nlist[index+1] = code[pos+(left_over/2)+i]
            index += 2
    n = get_numb_doubled_pairs(nlist)
    if n == 0:
        dic = get_odd_even_dic(nlist)
        return [0,dic[1]]
    return [n,0.0]

def phil_test(code):
    """
    AAAHJU's phillips test. input is list of code digits
    return list of 5 ic's: (1) Ave IC for 40 columns
    (2) ave ic for the 8 squares (3) ave IC for sqs 1 & 5
    (4) ave ic for sqs 2 & 8 (5) ave of (3) and (4)
    """
    limit = int(len(code)/40) # round to nearest 40 characters
    #ave fro the 40 columns
    col_ic  = [0.0]*40
    for index in range(40):
        freq = [0]*26
        count = 0
        for j in range(limit):
            freq[ code[j*40+index] ] += 1
            count += 1
        sum = 0.0
        for j in range(26):
            sum += freq[j]*(freq[j]-1)
        col_ic[index] = sum/(count*(count-1))
    ic = 0.0
    for j in range(40):
        ic += col_ic[j]
    ic /= 40
    result = [ic]
    # ave for the 8 squares
    sq_ic = [0.0]*8
    for index in range(8):
        freq = [0]*26
        count = 0
        for j in range(limit):
          for k in range(5):
            freq[ code[j*40+k+5*index] ] += 1
            count += 1
        sum = 0.0
        for j in range(26):
            sum += freq[j]*(freq[j]-1)
        sq_ic[index] = sum/(count*(count-1))
    ic = 0.0
    for j in range(8):
        ic += sq_ic[j]
    ic /= 8
    result.append(ic)
    #combine squares 1 & 5
    freq = [0]*26
    count = 0
    for j in range(limit):
      for k in range(5):
        freq[ code[j*40+k] ] += 1
        count += 1
        freq[ code[j*40+k+20] ] += 1
        count += 1
    sum = 0.0
    for j in range(26):
        sum += freq[j]*(freq[j]-1)
    ic1 = sum/(count*(count-1))
    result.append(ic1)
    #combine squares 2 and 8
    freq = [0]*26
    count = 0
    for j in range(limit):
      for k in range(5):
        freq[ code[j*40+5+k] ] += 1
        count += 1
        freq[ code[j*40+k+35] ] += 1
        count += 1
    sum = 0.0
    for j in range(26):
        sum += freq[j]*(freq[j]-1)
    ic2 = sum/(count*(count-1))
    result.append(ic2)
    ic = (ic1+ic2)/2
    result.append(ic)
    return result

# initialize sdd table
d = "03420010004526020443060035"
d = d + "00006000090700000000700070"
d = d + "30002006008000605000300000"
d = d + "16001000440000000001004010"
d = d + "00450000030032036540043800"
d = d + "30000500210000500204100000"
d = d + "20001006100000200100200000"
d = d + "50007000500000000000000000"
d = d + "00500040001137000053050008"
d = d + "00006000000000500000900000"
d = d + "00006000500004000000001000"
d = d + "20042000300700000000000070"
d = d + "55005000200000260000200060"
d = d + "00470080022000003004000000"
d = d + "02000800004055020400745000"
d = d + "30003000000500570600300000"
d = d + "00000000000000000000900000"
d = d + "10004000204000200000000050"
d = d + "11000001200000144014204000"
d = d + "00000008300000300000002000"
d = d + "04300050000623060653000006"
d = d + "00008000400000000000000000"
d = d + "60002006600000200000000000"
d = d + "30701000200000090005000600"
d = d + "16200200060020621021006000"
d = d + "20008000060100000000000009"
sdd = [None]*26
for i in range(26):
    sdd[i] = [0]*26
index = 0
for i in range(26):
    for j in range(26):
        sdd[i][j] = int(d[index])
        index += 1

def get_sdd_score(code):
    """
    return sdd score for code digits
    """
    sum = 0.0
    for i in range(len(code)-1):
        sum += sdd[ code[i] ][ code[i+1] ]
    score = 100*sum / (len(code)-1)
    return int(score)

#initialize AAHJU's log di table
d = "47874675736879373989676574"
d = d + "74208111630721710653712060"
d = d + "82527328727621822647613040"
d = d + "76568655843665753677656062"
d = d + "97888766745879775998577673"
d = d + "74537644722653840757624050"
d = d + "75547557732655752766635051"
d = d + "85449434831554842657625050"
d = d + "75877774425879764788473505"
d = d + "50004000300000500000600000"
d = d + "54327424622436531365304050"
d = d + "85578544825854852466655071"
d = d + "86438424710464761365614060"
d = d + "86788696846656853589656362"
d = d + "66776866636789772978968453"
d = d + "73337326721732760766603040"
d = d + "00000000000000000000600000"
d = d + "86679665836666863688656071"
d = d + "86768657846666874589747062"
d = d + "86658659833665962788747072"
d = d + "66766464623778560888334343"
d = d + "61008000700000500010210030"
d = d + "73347328722446730555214031"
d = d + "41424203510110350125202230"
d = d + "66666655633565863576436242"
d = d + "40005000300200300010200044"

logdi = [None]*26
for i in range(26):
    logdi[i] = [0]*26
index = 0
for i in range(26):
    for j in range(26):
        logdi[i][j] = int(d[index])
        index += 1

def decode_por_pair(c1,c2):
    """
    decode portax digraph
    """
    result = [0,0,0]
    if c1 < 13 : t_flag = 0
    else: t_flag = 2
    if (c2 % 2) > 0 : b_flag = 1
    else: b_flag = 0
    sum = t_flag + b_flag
    if sum is 2: #c1 bottom, c2 top
        if c1-13 <> (c2 >> 1) : # c1,c2 not verticaly aligned
            result = [1, (c2 >> 1)+13,(c1-13) << 1]
    if sum is 3: # c1,c2 both bottom
        if c1-13 <> (c2>>1) : # c2, c2 not vertically aligned
            result = [1,(c2>>1)+13,( (c1-13)<<1 )+1 ]
    return result

def score_portax(code,key_len):
    """
    given code digits and key length, return logdi score
    """
    big_step = 2*key_len
    count = 0.0
    score = 0.0
    for j in range(0,len(code),big_step):
        for k in range(key_len):
            if j+k+key_len >= len(code) : break
            c1 = code[j+k]
            c2 = code[j+k+key_len]
            #print j,k,j+k+key_len
            result = decode_por_pair(c1,c2)
            if result[0] is 1:
                c3 = result[1]
                c4 = result[2]
                score += logdi[c3][c4]
                count += 1
    score *= 100
    score /= count
    return score

def get_bif_dic(code,period):
    """
    get Gizmo's Bifid dic for code digits and period
    """
    def get_index(x,y): return x+26*y
    normalizer = 25*25 #25 possible ciphertext letters
    le = len(code)
    l1 = []
    l2 = []
    numb = 0
    for j in range(0,le,period):
        if j + period < le:
            limit = j + period
            second_row = int(period/2)
        else:
            limit = le
            second_row = int((le-j)/2)
        l1.extend( code[j : limit-second_row] )
        l2.extend( code[j+second_row : limit] )
        numb += limit-second_row - j
    list = map(get_index,l1,l2)
    sum = 0.0
    for i in range(26*26):
        sum += list.count(i)*(list.count(i)-1)
    dic = normalizer * sum / (numb*(numb-1))
    return dic

# T has compressed binary Single letter - Trigraph Discrepancy values
T=r"sP5D4475HAAPRphXWR=><I@A42p`E1"
T=T+r"N71rHAR2ApH2`M8BAiEW75A@uiAYU1"
T=T+r"r`NpS1IDR51@8D2@p5pI4PpTOO>D4p"
T=T+r"18;`QR6@p@Xonj`1p44s@4Xq6cQ822"
T=T+r"BrPq41r4262s4pRp4p2p@4111A44@p"
T=T+r"T8>4r1t1@@@458A1665pP`4v4tb7lX"
T=T+r":r4XS^V6s1p44p1:pPZnJ^q4r8q1rX"
T=T+r"bXNt1p8p1Pu@41118PX3xA4544Ap@@"
T=T+r"s8PU1v1p@rH1?22r1BRQy1p24hN_^?"
T=T+r"q1r2t@;@@2s@t911s4A@@P@@Qx@q11"
T=T+r"p4u2p:Cv@u2PQP2q@tjeW3E@82B6Y8"
T=T+r"@2@rB@p@BP8p<ApCAqR`NP1d5TT1hG"
T=T+r"S8HNiYApD4t@<@CIslG`@T4AIAQp2Q"
T=T+r"p421@6YI@H@435AqP68qA444S2p44w"
T=T+r"41:pPSH8RAT44q8q1rXPRC1r@1P8pA"
T=T+r"Ps@r115Hc[c3q@t@q44@p@s9r1v1q4"
T=T+r"4p\p6::sha[[1w@T24882Rr1p1424s"
T=T+r"P^hH:s@r@p8u4A@@rPx@4p11p4u@82"
T=T+r"I}2PQPr@xTA8N64Yq2Bp8q@rQp14{4"
T=T+r"p4r2s1q44qPp8s1t14p@65HAig_g1p"
T=T+r"@uhcWc31q`4H8Xr4p6VT`p@q@42TTA"
T=T+r":BTQD8RhT61UE8p8KTb<wH7XK@oU\5"
T=T+r"WCD6D4511p988qdD2sg1\F4A9FD1QJ"
T=T+r"9p1@p\CH26NliaAp2P<p2:Hp1paPp1"
T=T+r"p1p@@tAT2p887Rq81r2p@{@p22@p8q"
T=T+r"144p4A@@1qXs4t4A1114p61p8Dr1u1"
T=T+r"v;`S2r@PT@`4s4A@@qXq22p82p@rPw"
T=T+r"22t4@q4pB@t14p4pPdZ1q1t41@@@p1"
T=T+r"p1sPp@t8v@qH88s`O]neNAAAHE2Q1p"
T=T+r":pPX4H6hp6pQ48p4s7B1J2s1P88AT4"
T=T+r"4v1pT:8;PEeF6s1p14p@p@qPPpV9]Y"
T=T+r"v1tHp62sPl_RQr@tAT2pH<7R;q1p8p"
T=T+r"2p@sZ8hHs@q6@p81q444p@@2pS@i4w"
T=T+r"@4p111Dp54@p@2aZIv@uCPS1sPonjn"
T=T+r"y8qJcYK2p@r1u\?o^?sLTV71p2y`dW"
T=T+r"><x1p@xX_f>4u4tPp8y@6q@meVCU5:"
T=T+r"p4Q@2RhaWSU7:64C4`Dr[T7:>41P8p"
T=T+r"oQXpU7F6D64A@pQqT7fF6sn38pTE;>"
T=T+r"4GThIq@p41rFph@sl?o>=p1pPl3Z11"
T=T+r"w@P2ph97Rq81r2p@s18:Ps@q2@48qA"
T=T+r"4441@rW8Z@1444t4p11I4251q42Olk"
T=T+r"lx41p83PSp2q@p:T@@s4r@4XqjRS91"
T=T+r"p@rPq4t2u4pTp4p2@@s1444q28x41p"
T=T+r"@@FU@Aq6Pz4q1q`ph:th_VdMN@H@Aq"
T=T+r"1Pp:pPkfb>hAV3U7H44qPpep84yPqP"
T=T+r"wVZ?KU7nN6s1p44uP@8^;=S|8p6ulS"
T=T+r"YA5p@@tAPRphl?f>q1r2p@sglhOs@p"
T=T+r"J2@p9p1p4T44A@qPHZp1p14s@4111A"
T=T+r"44pD@8pb[JIv@t8;PQPr@8olZ^r44A"
T=T+r"p@p4Xq6cQ86@BrPq41qh6_>5s4pRp4"
T=T+r"p2@r1pA44D8488p4@p1s41@@@FeIA1"
T=T+r"4p4Lpb8v4qAp@`pXXt@p2p@NmkmD4P"
T=T+r"Q118qPqPh@VA5A82p1qHslOoN51p1p"
T=T+r"VP<pPADN4p1q^o[KQ3N6DomkM6q2T7"
T=T+r"9FD11@9~p4q2u`3RAq@@t1p2pXK:>5"
T=T+r"q1r2uO8h:s@s411@t@@pPCjH@x4q1p"
T=T+r"4~v8p2PQu2:Hx@4X8pVkSI2pBrPpP4"
T=T+r"1p2x4PVA4p2r11pA44@X8Z>4r1t1@@"
T=T+r"@FUhAA42Uq@w4q@@p`7lXZ@q42p681"
T=T+r"|omiN|Pp1Q~q@s2pP~xRz8PSP1w8PY"
T=T+r"AX?_>GpQqAP64889Rq11rRp@pP81w@"
T=T+r"p:4PNmj5hc_C5p@pP22s8t@EpY11q4"
T=T+r"4@8BRs1s1@r11p2Pq4p8qbH8}B8s@r"
T=T+r"PuX5:^1~q@rP~@s1s8I^85}Hq14p40"

# read T and put it into the working binary trigraph table: bstd
n = 26*26*26
bstd = [0]*n
i = index = 0
count = 0
while i < n:
    c = T[index]
    index +=1
    x = ord(c)-ord('0')
    if x > 63:
        x -= 63
        for j in range(6*x):
            bstd[i] = 0
            i += 1

    else:
        mask = 1
        while mask < 64:
            if mask & x :
                bstd[i] = 1
                count += 1
            else: bstd[i] = 0
            i += 1
            mask += mask
            if i >= n : break;

def get_bstdvalue(x,y,z) : return bstd[ x+26*y+26*26*z ]

def get_bstd_score(code,period):
    """
    given code digits and period, return binary STD score for
    the corresponding complete columnar or nihilist transposition
    """
    def get_col_score(c,col_key,number_rows,column,period):
        score = best_col = 0
        for col in range(c,period):
            n = 0
            for r in range(number_rows):
                x1 = column[col_key[c-2]][r]
                x2 = column[col_key[c-1]][r]
                x3 = column[col_key[col]][r]
                n += get_bstdvalue(x1,x2,x3)
            if n > score:
                score = n
                best_col = col
        return [score,best_col]

    number_rows = len(code) / period
    column = [None]*period
    index = 0
    for c in range(period):
        column[c] = code[index:index+number_rows]
        index += number_rows

    cols_used = [0]*period
    col_key = [0]*period
    score = 0
    for c0 in range(period):
        cols_used[c0] = 1
        col_key[0] = c0
        for c1 in range(period):
            if cols_used[c1] : continue
            cols_used[c1] = 1
            col_key[1] = c1
            n = 2
            for c in range(period):
                if cols_used[c] : continue
                col_key[n] = c
                n += 1
            temp_score = 0
            for c in range(2,period):
                result = get_col_score(c,col_key,number_rows,column,period)
                temp_score += result[0]
                n = col_key[result[1]]
                col_key[ result[1] ] = col_key[c]
                col_key[c] = n
            if temp_score > score : score = temp_score
            cols_used[c1] = 0
        cols_used[c0] = 0
    std_score = 100*score/(number_rows*(period-2))
    return std_score

def next_per(str,le):
    """
    get next permutation of string str of length le
    return 0 if finished, 1 otherwise.
    """
    if le < 2: return 0
    #find last element not in reverse alphabetic order
    last = le-2
    while str[last] >= str[last+1]:
        if last is 0 : return 0
        last -= 1

    # find first element that is larger than the element at last
    fst = le-1
    while str[fst] <= str[last]:
        fst -= 1

    #swap these two
    c = str[last]
    str[last] = str[fst]
    str[fst] = c

    #put part of string at tail into ascending order
    if str[last+1] != str[le-1] :
        i = 1
        while last+i < le -i:
            c = str[last+i]
            str[last+i] = str[le-i]
            str[le-i] = c
            i += 1
    return 1


def swag_test(code,period):
    """
    test code digits for swagman of given period, return binary std score
    and best scoring line
    """
    def score_row(row):
        score = 0
        for i in range(len(row)-2):
            score += get_bstdvalue(row[i],row[i+1],row[i+2])
        return score

    def construct_row(row_order,swag_array,period,numb_columns):
        row = []
        index = 0
        for i in range(numb_columns):
            c = swag_array[ row_order[index] ][i]
            row.append(c)
            index += 1
            if index == period : index = 0
        return row

    numb_columns = len(code)/period
    row_order = []
    for i in range(period):
        row_order.append(i)
    swag_array = [None]*period
    for i in range(period):
        swag_array[i] = [0]*numb_columns
    index = i = 0
    for c in code:
        swag_array[i][index] = c
        i += 1
        if i == period :
            index += 1
            i = 0
    row = construct_row(row_order,swag_array,period,numb_columns)
    score = score_row(row)
    best_score = score
    best_row = row
    while next_per(row_order,len(row_order)) != 0:
        row = construct_row(row_order,swag_array,period,numb_columns)
        score = score_row(row)
        if score > best_score:
            best_score = score
            best_row = row
    std_score = 100*best_score / (numb_columns-2)
    l1 = convert_to_string(best_row)
    return [std_score,l1]

# AAHJU's vigenere family tests:
VSLIDEFAIR = 0
BSLIDEFAIR = 1
VIGENERE = 2
VARIANT = 3
BEAUFORT = 4
VAUTOKEY = 5
BAUTOKEY = 6
VEAUTOKEY = 7
PORTA = 8
PAUTOKEY = 9

def decode_let(ct,key,ciph_type):
    if ciph_type is VIGENERE or ciph_type is VEAUTOKEY:
        cp = (26+ct-key)%26
    elif ciph_type is VARIANT or ciph_type is VAUTOKEY:
        cp = (ct+key)%26
    elif ciph_type is BEAUFORT or ciph_type is BAUTOKEY:
        cp = (26+key-ct)%26
    else: # PORTA
        key = key/2
        cp = ct
        if cp < 13:
            cp += key
            if cp < 13: cp += 13
        else:
            cp -= key
            if cp > 12: cp -= 13
    return cp

def best_di(col,ciph_type,code,period):
    best_score = 0
    rows = int(len(code)/period)
    for kl in range(26):
        for kr in range(26):
            score = 0
            ct = 0
            kl1 = kl
            kr1 = kr
            for j in range(rows):
                if col+j*period+1 >= len(code): break
                cl = code[col+j*period]
                cr = code[col+1+j*period]
                pl = decode_let(cl,kl1,ciph_type)
                pr = decode_let(cr,kr1,ciph_type)
                score += logdi[pl][pr]
                ct += 1
                if ciph_type != PORTA and ciph_type >= VAUTOKEY:
                    kl1 = pl
                    kr1 = pr
            score *= 100
            score /= ct
            if score > best_score:
                best_score = score
    return best_score

def decode_sl(cl,cr,k,ciph_type):
    if ciph_type is BSLIDEFAIR:
        return [(26+k-cr)%26,(26+k-cl)%26]
    return [ (26+cr-k)%26,(cl+k)%26]

def best_sldi(col,ciph_type,code,period):
    best_score = 0
    rows = int(len(code)/ (2*period))
    rowb = 2*col
    for k in range(26):
        score = 0
        ct = 0
        for j in range(rows):
            posn = j*period*2+rowb
            if posn+1 >= len(code): break
            cl = code[posn]
            cr = code[posn+1]
            result = decode_sl(cl,cr,k,ciph_type)
            score += logdi[ result[0] ][ result[1] ]
            ct += 1
        score *= 100
        score /= ct
        if score > best_score :
            best_score = score
    return best_score


def vigtests(code,min_period,max_period):
    cipher_names = ["Vigenere Slidefair","Beaufort Slidefair ","Vigenere or Variant ","Variant ",\
            "Beaufort ","Variant Autokey ","Beaufort Autokey ",\
            "Vigenere Autokey","Porta ","Porta Autokey"]

    if (len(code) & 1) :
        start = 2 # odd length skip slidefairs
    else : start = 0
    best_score = 0
    for ciph_type in range(start,10):
        if ciph_type is VARIANT : continue #same score as Vigenere
        #print "Testing ",cipher_names[ciph_type]
        for period in range(min_period,max_period):
            sum = 0
            for col in range(period):
                if ciph_type > BSLIDEFAIR:
                    sum += best_di(col,ciph_type,code,period)
                else:
                    sum += best_sldi(col,ciph_type,code,period)
            sum /= period
            if sum > best_score:
                best_score = sum
                best_period = period
                best_type = ciph_type
    return[ best_score, best_period, cipher_names[best_type] ]

#encode and decode the Vigenere family

def encode_slet(pl,pr,kl,ciph_type=0):
    """
    encode pair pl,pr with key letter kl.
    """
    if ciph_type == VSLIDEFAIR:
        if pl== (26+pr-kl)%26: return [ (pl+1)%26,(pr+1)%26 ]
        return [ (26+pr-kl)%26,(26+pl+kl)%26]
    elif ciph_type == BSLIDEFAIR:
        if pr == (kl-pl+26)%26:
            return [ (pl+1)%26,(pr+25)%26]
        return [(kl-pr+26)%26,(kl-pl+26)%26]
    return "ERROR"

def decode_slet(cl,cr,kl,ciph_type=0):
    """
    decode pair cl,cr with key letter kl.
    """
    if ciph_type == VSLIDEFAIR:
        if cl== (26+cr-kl)%26: return [ (cl+25)%26,(cr+25)%26 ]
        return [ (26+cr-kl)%26,(26+cl+kl)%26]
    elif ciph_type == BSLIDEFAIR:
        if cr == (kl-cl+26)%26:
            return [ (cl+25)%26,(cr+1)%26]
        return [(kl-cr+26)%26,(kl-cl+26)%26]
    return "ERROR"

def slidefair_encode(plaintext,key,ciph_type=0):
    """
    slidefair encode string plaintext with string key using the
    ciph_type digit.
    """
    plain = convert_string(plaintext)
    if len(plain) & 1 :
        print "Odd number of letters!"
        return "ERROR"
    key_code = convert_string(key)
    code = [None]*len(plain)
    period = len(key_code)
    for col in range(period):
        pos = 2*col
        kl = key_code[col]
        while pos < len(plain):
            code[pos:pos+2] = encode_slet(plain[pos],plain[pos+1],kl,ciph_type=ciph_type)
            pos += 2*period
    codetext = convert_to_string(code)
    return codetext

def slidefair_decode(codetext,key,ciph_type=0):
    """
    decode string codetext with string key using the
    ciph_type digit.
    """
    code = convert_string(codetext)
    key_code = convert_string(key)
    plain = [None]*len(code)
    period = len(key_code)
    for col in range(period):
        pos = 2*col
        kl = key_code[col]
        while pos < len(code):
            plain[pos:pos+2] = decode_slet(code[pos],code[pos+1],kl,ciph_type=ciph_type)
            pos += 2*period
    plaintext = convert_to_string(plain)
    return plaintext

def encode_let(cp,key,ciph_type):
    if ciph_type is VIGENERE or ciph_type is VEAUTOKEY:
        ct = (cp+key)%26
    elif ciph_type is VARIANT or ciph_type is VAUTOKEY:
        ct = (26+cp-key)%26
    elif ciph_type is BEAUFORT or ciph_type is BAUTOKEY:
        ct = (26+key-cp)%26
    else: # PORTA
        k = key/2
        ct = cp
        if ct < 13:
            ct += k
            if ct < 13: ct += 13
        else:
            ct -= k
            if ct > 12: ct -= 13
    return ct

def vig_family_encode(plaintext,key,ciph_type):
    """
    encode string plaintext with string key using the
    ciph_type digit.
    """
    if ciph_type <= BSLIDEFAIR:
        return slidefair_encode(plaintext,key,ciph_type)
    plain = convert_string(plaintext)
    key_code = convert_string(key)
    code = [None]*len(plain)
    period = len(key_code)
    for col in range(period):
        pos = col
        kl = key_code[col]
        while pos < len(plain):
            code[pos] = encode_let(plain[pos],kl,ciph_type)
            if ciph_type != PORTA and ciph_type >= VAUTOKEY:
                kl = plain[pos]
            pos += period
    codetext = convert_to_string(code)
    return codetext

def vig_family_decode(codetext,key,ciph_type):
    """
    decode string codetext with string key using the
    ciph_type digit.
    """
    if ciph_type <= BSLIDEFAIR:
        return slidefair_decode(codetext,key,ciph_type)
    code = convert_string(codetext)
    key_code = convert_string(key)
    plain = [None]*len(code)
    period = len(key_code)
    for col in range(period):
        pos = col
        kl = key_code[col]
        while pos < len(code):
            plain[pos] = decode_let(code[pos],kl,ciph_type)
            if ciph_type != PORTA and ciph_type >= VAUTOKEY:
                kl = plain[pos]
            pos += period
    plaintext = convert_to_string(plain)
    return plaintext

#Nicodemus routines
def nicodemus_encode(plaintext,key,ciph_type = VIGENERE):
    """
    input strings plaintext and key, output nicodemus
    code string.
    """
    plain = convert_string(plaintext)
    key_code = convert_string(key)
    offset = get_hat_offset(key)
    le = len(plain)
    keyl = len(key)
    start_pos = 0
    limit = 5* keyl
    code = []
    while start_pos < le:
        if start_pos+limit > le:
            limit = le-start_pos
        for index in range(keyl):
            for i in range(start_pos,start_pos+limit):
                if  i % keyl  == offset[index]:
                    code.append( encode_let(plain[i],key_code[ i % keyl],\
                    ciph_type=ciph_type) )
        start_pos += limit
    codetext = convert_to_string(code)
    return codetext

def nicodemus_decode(codetext,key,ciph_type = VIGENERE):
    """
    input strings codetext and key, output nicodemus
    plaintext string.
    """
    code = convert_string(codetext)
    key_code = convert_string(key)
    offset = get_hat_offset(key)
    le = len(code)
    keyl = len(key)
    start_pos = 0
    limit = 5* keyl
    plain = [None]*le
    count = 0
    while start_pos < le:
        if start_pos+limit > le:
            limit = le-start_pos
        for index in range(keyl):
            for i in range(start_pos,start_pos+limit):
                if  i % keyl  == offset[index]:
                    plain[i] = decode_let(code[count],key_code[ i % keyl ],\
                    ciph_type = ciph_type)
                    count += 1
        start_pos += limit
    plaintext = convert_to_string(plain)
    return plaintext

#Progressive key routines
def progressive_key_encode(plaintext,key,index,first_ciph_type,second_ciph_type):
    """
    input strings plaintext and key, and integers index, first_ciph_type,
    and second_ciph_type. Output progressive key codetext string.
    """
    first_codetext = vig_family_encode(plaintext,key,first_ciph_type)
    first_code = convert_string(first_codetext)
    key_code = convert_string(key) #convert in case of blanks in key
    period = len(key_code)
    key2 = count = 0
    code = []
    for c in first_code:
        code.append( encode_let(c,key2,second_ciph_type) )
        count += 1
        if count == period:
            count = 0
            key2 = (key2+index) % 26
    codetext = convert_to_string(code)
    return codetext

def progressive_key_decode(codetext,key,index,first_ciph_type,second_ciph_type):
    """
    input strings codetext and key, and integers index, first_ciph_type,
    and second_ciph_type. Output progressive key plaintext string.
    """
    first_code = convert_string(codetext)
    key_code = convert_string(key) #convert in case of blanks in key
    period = len(key_code)
    key2 = count = 0
    code = []
    for c in first_code:
        code.append( decode_let(c,key2,second_ciph_type) )
        count += 1
        if count == period:
            count = 0
            key2 = (key2+index) % 26
    first_codetext = convert_to_string(code)
    plaintext = vig_family_decode(first_codetext,key,first_ciph_type)
    return plaintext

#running key encode and decode routines
def running_key_encode(plaintext,ciph_type = VIGENERE):
    """
    encode string plaintext as running key using ciph_type
    giving the cipher type.
    """
    plain = convert_string(plaintext)
    plain = convert_to_string(plain)
    if len(plain) & 1:
        plain += 'x'
    n = len(plain)/2
    key = plain[ :n]
    pl = plain[n:]
    codetext = vig_family_encode(pl,key,ciph_type)
    return codetext

def running_key_decode(codetext,key,ciph_type = VIGENERE):
    """
    decode string codetext with string key as running key using ciph_type
    giving the cipher type.
    """
    c1 = convert_string(codetext)
    c2 = convert_string(key)
    if len(c1) != len(c2) :
        print "Key and codetext different lengths!"
        return "ERROR"
    plain = vig_family_decode(codetext,key,ciph_type)
    plaintext = key + plain
    return plaintext

#routines for route transposition
def in_route(plain,matrix,route,rwidth,rheight):
    index = 0
    if route == 0:#HORIZONTAL:
            for row in range(rheight):
                for col in range(rwidth):
                    matrix[row][col] = plain[index]
                    index += 1
    elif route ==1:# VERTICAL:
            for col in range(rwidth):
                for row in range(rheight):
                    matrix[row][col] = plain[index]
                    index += 1
    elif route == 2:#DIAGONAL:
            for k in range(rwidth+rheight):
                for col in range(rwidth):
                    if k>=col and k-col<rheight:
                        matrix[k-col][col] = plain[index]
                        index += 1
    elif route == 9:#REV_DIAGONAL:
            for k in range(rwidth+rheight):
                for col in range(rwidth-1,-1,-1):
                    if k>=col and k-col<rheight:
                        matrix[k-col][col] = plain[index]
                        index += 1                      
    elif route == 3:#ALT_DIAGONAL:
            dr=0    
            for k in range(rwidth+rheight):
                if dr==0:
                    for col in range(rwidth):
                        if k>=col and k-col<rheight:
                            matrix[k-col][col] = plain[index]
                            index += 1
                else:
                    for col in range(rwidth-1,-1,-1):
                        if k>=col and k-col<rheight:
                            matrix[k-col][col] = plain[index]
                            index += 1
                dr ^= 1
    elif route == 4:#REV_ALT_DIAGONAL:
            dr=1    
            for k in range(rwidth+rheight):
                if dr==0:
                    for col in range(rwidth):
                        if k>=col and k-col<rheight:
                            matrix[k-col][col] = plain[index]
                            index += 1
                else:
                    for col in range(rwidth-1,-1,-1):
                        if k>=col and k-col<rheight:
                            matrix[k-col][col] = plain[index]
                            index += 1
                dr ^= 1
    elif route==5:#SPIRAL:
        wd,ht,sx,sy= rwidth,rheight,0,0
        cnt = rwidth * rheight        
        while cnt > 0:
            for j in range(sx,wd):
                matrix[sy][j]=plain[index]
                index += 1
                cnt -= 1
            if cnt == 0 : break
            for j in range(sy+1,ht):
                matrix[j][wd-1]=plain[index]
                index += 1
                cnt -= 1
            if cnt == 0 : break                
            for j in range(wd-2,sx-1,-1):
                matrix[ht-1][j]=plain[index]
                index += 1
                cnt -= 1
            if cnt == 0 : break                
            for j in range(ht-2,sy,-1):
                matrix[j][sx]=plain[index]
                index += 1
                cnt -= 1
            wd -=1
            ht -=1
            sx +=1
            sy +=1
    elif route==6:#ALT_VERTICAL:
        index = 0
        dr=0
        for col in range(rwidth):
            if dr==0:
                for row in range(rheight):
                    matrix[row][col]=plain[index]
                    index +=1
            else:
                for row in range(rheight):
                    matrix[rheight-1-row][col]=plain[index]
                    index +=1
            dr ^= 1
    elif route==7:#ALT_HORIZONTAL:
        index = 0
        dr=0
        for row in range(rheight):
            if dr==0:
                for col in range(rwidth):
                    matrix[row][col]=plain[index]
                    index +=1
            else:
                for col in range(rwidth):
                    matrix[row][rwidth-1-col]=plain[index]
                    index +=1
            dr ^= 1
    elif route==8:#LEFT_SPIRAL:
        wd,ht,sx,sy= rwidth,rheight,0,0
        cnt = rwidth * rheight                
        while cnt > 0:
            for j in range(sy,ht):
                matrix[j][sx]=plain[index]
                index += 1
                cnt -= 1
            if cnt == 0 : break                
            for j in range(sx+1,wd):
                matrix[ht-1][j]=plain[index]
                index += 1
                cnt -= 1
            if cnt == 0 : break                
            for j in range(ht-2,sy-1,-1):
                matrix[j][wd-1]=plain[index]
                index += 1
                cnt -= 1
            if cnt == 0 : break                
            for j in range(wd-2,sx,-1):
                matrix[sy][j]=plain[index]
                index += 1
                cnt -= 1
            wd -=1
            ht -=1
            sx +=1
            sy +=1

                        
def out_route(route,matrix,rwidth,rheight):
    code = []
    if route == 0:#HORIZONTAL:
            for row in range(rheight):
                for col in range(rwidth):
                    code.append(matrix[row][col])
    elif route == 1:#VERTICAL:
            for col in range(rwidth):
                for row in range(rheight):
                    code.append(matrix[row][col])               
    elif route == 2:#DIAGONAL:
            for k in range(rwidth+rheight):
                for col in range(rwidth):
                    if k>=col and k-col<rheight:
                        code.append(matrix[k-col][col])
    elif route == 9:#REV_DIAGONAL:
            for k in range(rwidth+rheight):
                for col in range(rwidth-1,-1,-1):
                    if k>=col and k-col<rheight:
                        code.append(matrix[k-col][col])                     
    elif route == 3:#ALT_DIAGONAL:
            dr=0    
            for k in range(rwidth+rheight):
                if dr==0:
                    for col in range(rwidth):
                        if k>=col and k-col<rheight:
                            code.append(matrix[k-col][col])
                else:
                    for col in range(rwidth-1,-1,-1):
                        if k>=col and k-col<rheight:
                            code.append(matrix[k-col][col])
                dr ^= 1
    elif route == 4:#REV_ALT_DIAGONAL:
            dr=1    
            for k in range(rwidth+rheight):
                if dr==0:
                    for col in range(rwidth):
                        if k>=col and k-col<rheight:
                            code.append(matrix[k-col][col])
                else:
                    for col in range(rwidth-1,-1,-1):
                        if k>=col and k-col<rheight:
                            code.append(matrix[k-col][col])
                dr ^= 1
    elif route==5:#SPIRAL:
        wd,ht,sx,sy= rwidth,rheight,0,0
        cnt = rwidth * rheight
        while cnt > 0:
            for j in range(sx,wd):
                code.append(matrix[sy][j])
                cnt -=1
            if cnt == 0 : break
            for j in range(sy+1,ht):
                code.append(matrix[j][wd-1])
                cnt -= 1
            if cnt == 0 : break
            for j in range(wd-2,sx-1,-1):
                code.append(matrix[ht-1][j])
                cnt -= 1
            if cnt == 0 : break
            for j in range(ht-2,sy,-1):
                code.append(matrix[j][sx])
                cnt -= 1
            wd -=1
            ht -=1
            sx +=1
            sy +=1
    elif route==6:#ALT_VERTICAL:
        index = 0
        dr=0
        for col in range(rwidth):
            if dr==0:
                for row in range(rheight):
                    code.append(matrix[row][col])
            else:
                for row in range(rheight):
                    code.append(matrix[rheight-1-row][col])
            dr ^= 1
    elif route==7:#ALT_HORIZONTAL:
        index = 0
        dr=0
        for row in range(rheight):
            if dr==0:
                for col in range(rwidth):
                    code.append(matrix[row][col])
            else:
                for col in range(rwidth):
                    code.append(matrix[row][rwidth-1-col])
            dr ^= 1
    elif route==8:#LEFT_SPIRAL:
        wd,ht,sx,sy= rwidth,rheight,0,0
        cnt = rwidth * rheight        
        while cnt > 0:
            for j in range(sy,ht):
                code.append(matrix[j][sx])
                cnt -= 1
            if cnt == 0 : break                
            for j in range(sx+1,wd):
                code.append(matrix[ht-1][j])
                cnt -= 1
            if cnt == 0 : break                    
            for j in range(ht-2,sy-1,-1):
                code.append(matrix[j][wd-1])
                cnt -= 1
            if cnt == 0 : break                
            for j in range(wd-2,sx,-1):
                code.append(matrix[sy][j])
                cnt -= 1
            wd -=1
            ht -=1
            sx +=1
            sy +=1  
    return code                 
                    
def flip_route(route,matrix,rwidth,rheight):
    if route==0:#NO_FLIP: 
        return
    elif route==1 or route==3:#HORIZONTAL_FLIP or COMBINED_FLIP
        for row in range(rheight):
            matrix[row].reverse()
    if route == 2 or route == 3:#VERTICAL_FLIP or COMBINED_FLIP
        for col in range(rwidth):
            temp = [matrix[row][col] for row in range(rheight)]
            temp.reverse()
            for row in range(rheight):
                matrix[row][col] = temp[row]

def route_encrypt_decrypt(text,rwidth,r_in,r_flip,r_out,reverse_in=0,reverse_out=0,include_digits=0):
    """
    given plaintext/ciphertext string 'text', and integers rwidth: width 
    of the text block,  r_in: the input route, r_flip: the flip number, 
    and r_out: the output route, return the ciphertext/plaintext 
    as a lowercase string.
    if reverse_in is included and non-zero, reverse the input text string.
    if reverse_out is included and non-zero, reverse the output test string
    if 'print_matrix' is included and non-zero, print the matrix to the screen
    """
    symbols = 'abcdefghijklmnopqrstuvwxyz'
    if include_digits == 1:
        symbols += '0123456789'
    plain = [c for c in text.lower() if c in symbols]
    if reverse_in:
        plain.reverse()
    rheight = len(plain)/rwidth
    if rwidth*rheight != len(plain):
        print "inconsistent width!"
        return "Error"
    matrix = [[ ]]*rheight
    for r in range(rheight):
        matrix[r]=[r]*rwidth
    in_route(plain,matrix,r_in,rwidth,rheight)
    flip_route(r_flip,matrix,rwidth,rheight)
    code = out_route(r_out,matrix,rwidth,rheight)
    if reverse_out:
        code.reverse()
    return [''.join(code),matrix]

#numbered key routines
def get_shifted_extended_key(key,shift):
    """
    input string 'key' and integer 'shift'. output shifted extended key string
    """
    upperC="ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    key = key.upper()
    k_array = [c for c in key if c in upperC]
    k_ext = ''.join(k_array)
    for c in upperC:
        if c not in k_ext:
            k_ext += c
    k_ext_shift = k_ext[shift:]+k_ext[0:shift]
    return k_ext_shift

def numbered_key_encode(plaintext,key,shift=0):
    """
    input string 'plaintext' and  string 'key' . 'shift' is integer. output
    numbered key encoded codetext.
    """
    plain = convert_string(plaintext)
    key = get_shifted_extended_key(key,shift)
    nkey = convert_string(key)
    inverse_key = [None]*26
    for i in range(26):
        inverse_key[i] = []
    for n in range(26):
        for i in range(len(key)):
                if n == nkey[i]:
                    s = "%02d"%( i )
                    inverse_key[n].append(s )
    code = []
    for c in plain:
        n = randrange( len(inverse_key[c]) )
        code.append( inverse_key[c][n] )
    codetext = "".join(code)
    return [codetext,key]

def numbered_key_decode(codetext,key,shift=0):
    """
    input string codetext and string 'key'. 'shift' is integer. Output
    numbered key decoded plaintext string.
    """
    code = convert_numb_string(codetext)
    if len(code) & 1:
        print "Odd numbers of digits!"
        return "ERROR"
    key = get_shifted_extended_key(key,shift)       
    nkey = convert_string(key)      
    plain = []
    for i in range(0,len(code),2):
        plain.append( nkey[ 10*code[i]+ code[i+1] ])
    plaintext = convert_to_string(plain)
    return [plaintext,key]
    
def expand_key(key):
    """
    input key string and return 26 letter expanded key string
    """
    alpha = 'abcdefghijklmnopqrstuvwxyz'
    key = key.lower()
    expanded_key = ''
    for c in key:
        if c in alpha and c not in expanded_key:
            expanded_key += c
    for c in alpha:
        if c not in expanded_key:
            expanded_key += c
    return expanded_key
    
def simp_sub_encode(plaintext,key,shift,key_type,key2='',word_div=0):
    alpha = 'abcdefghijklmnopqrstuvwxyz'
    shift = shift%26
    ex_key = expand_key(key)
    ex_key2 = expand_key(key2) # default is alphabetical order
    if key_type=='k1':
        pkey = ex_key
        ckey = ex_key2
    elif key_type == 'k2':
        pkey = ex_key2
        ckey = ex_key
    elif key_type == 'k3':
        pkey = ex_key
        ckey = ex_key
    else:
        pkey = ex_key2 # should be non-alphabetical order this time
        ckey = ex_key
    if key_type == 'k1':
        pkey = pkey[shift:]+pkey[0:shift]
    else:
        ckey = ckey[shift:]+ckey[0:shift]
    plain = plaintext.lower()
    code = ''
    for c in plain:
        if c in alpha:
            n = pkey.index(c)
            code += ckey[n]
        elif word_div != 0:
            code += c
    code = code.upper()
    return [code,pkey,ckey]

def simp_sub_decode(codetext,key,shift,key_type,key2='',word_div=0):
    alpha = 'abcdefghijklmnopqrstuvwxyz'
    shift = shift%26    
    ex_key = expand_key(key)
    ex_key2 = expand_key(key2) # default is alphabetical order
    if key_type=='k1':
        pkey = ex_key
        ckey = ex_key2
    elif key_type == 'k2':
        pkey = ex_key2
        ckey = ex_key
    elif key_type == 'k3':
        pkey = ex_key
        ckey = ex_key
    else:
        pkey = ex_key2 # should be non-alphabetical order this time
        ckey = ex_key
    if key_type == 'k1':
        pkey = pkey[shift:]+pkey[0:shift]
    else:
        ckey = ckey[shift:]+ckey[0:shift]
    code = codetext.lower()
    plain = ''
    for c in code:
        if c in alpha:
            n = ckey.index(c)
            plain += pkey[n]
        elif word_div != 0:
            plain += c
    return [plain,pkey,ckey]
    