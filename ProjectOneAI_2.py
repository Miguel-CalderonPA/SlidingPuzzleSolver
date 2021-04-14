'''
Miguel Calderon
Date: 2/2/2021
CSC 535 Artificial Intelligence
Last Modification: 2/11/2021
Professor Ian MacDonald
'''

# Imports
from queue import PriorityQueue
import math
import copy
import random

# Constants
PUZZLE_SIZE = 9
ROW_SIZE = int(math.sqrt(int(PUZZLE_SIZE)))
GOAL = '12345678'
Q_SIZE = 100000


# TESTING CASES ----------------------
# Solvable
INPUT1 = "123045678"
INPUT2 = "182043765"
INPUT3 = "123405678"
INPUT4 = "130425786"
INPUT5 = "813402765"
INPUT6 = "013425786"
INPUT7 = "180432576"
INPUT8 = "876543210"

# Unsolvable
INPUT9 = "125436708"
INPUT10 = "812043765"
INPUT11 = "123456870"
INPUT12 = "123804765"
INPUT13 = "134862705"
INPUT14 = "281043765"
INPUT15 = "281463075"
INPUT16 = "567408321"
INPUT17 = "123456870"
INPUT18 = "283164705"

# ------------------------------------------------------------------------
# PRE: Needs input
# POST: returns if input is valid
# PURPOSE: checks to see if the user input is a valid puzzle
def ValidInput(input):
    if len(set(input)) != PUZZLE_SIZE or not input.isnumeric():  # is its not length of 9 and not a number
        return False
    else:
        for i in range(9): # if valid until now, check to see if it has every digit 0-8
            if str(i) not in input:
                return False
    return True


# ------------------------------------------------------------------------
# PRE: needs puzzle
# POST: returns if puzzle is solvable
# PURPOSE: takes in a valid puzzle and determines if its even solvable
def isPossible(puzzle):
    # basically a fancy away of classifying a number is greater than a number later in the array "inversion"
    inversions = 0
    for elem in range(len(puzzle)):
        for otherVals in range(elem + 1, len(puzzle)): # checks each number after current position
            mainVal = int(puzzle[elem])
            other = int(puzzle[otherVals])
            if mainVal > other and mainVal != 0 and other != 0: # as long as the next val is larger and both vals aren't 0 then its an inversion
                inversions += 1
    if inversions % 2 == 0: # even inversions mean solvable
        return True
    else: # odd inversions mean unsolvable
        return False


# ------------------------------------------------------------------------
# PRE: Needs 2 states to compare
# POST: returns MHS of function
# PURPOSE: It calculates the distance for each point in the array
def Manhattan_Distance_Function(currentState, goalState):
    distance = 0
    for i in GOAL:
        currentIndex = currentState.index(i)
        goalIndex = goalState.index(i)
        rowDist = abs(int(currentIndex / 3) - (int(goalIndex / 3)))  # take indices & divides by 3 because of 3x3 board
        colDist = abs(int(currentIndex % 3) - (int(goalIndex % 3)))  # after rows are counted, we count columns
        distance += rowDist + colDist # add rows & column distances
    return distance


# ------------------------------------------------------------------------
# PRE: needs board
# POST: returns puzzle with slide up if possible
# PURPOSE: slides a puzzle piece up by one block
def moveUp(board):
    emptyIndex = board.index("0")  # find empty block
    if emptyIndex > 5:  # if not possible
        board = [9] * 9  # fills with invalid numbers to allow it to be flagged later
        return board
    else:
        swapIndex = emptyIndex + ROW_SIZE
    # slide
    temp = board[swapIndex]
    board[swapIndex] = board[emptyIndex]
    board[emptyIndex] = temp
    return board


# ------------------------------------------------------------------------
# PRE: needs board
# POST: returns puzzle with slide left if possible
# PURPOSE: slides a puzzle piece to the left by one block
def moveLeft(board):
    emptyIndex = board.index("0")  # find empty block
    if emptyIndex % 3 == 2:  # if invalid
        board = [9] * 9  # fills with invalid numbers to allow it to be flagged later
        return board
    else:
        swapIndex = emptyIndex + 1
    # slide
    temp = board[swapIndex]
    board[swapIndex] = board[emptyIndex]
    board[emptyIndex] = temp
    return board


# ------------------------------------------------------------------------
# PRE:needs board
# POST: returns puzzle with slide down if possible
# PURPOSE: slides a puzzle piece down by one block
def moveDown(board):
    emptyIndex = board.index("0")  # find empty block
    if emptyIndex < 3:
        board = [9] * 9  # fills with invalid numbers to allow it to be flagged later
        return board
    else:
        swapIndex = emptyIndex - ROW_SIZE
    # Slide
    temp = board[swapIndex]
    board[swapIndex] = board[emptyIndex]
    board[emptyIndex] = temp
    return board


# ------------------------------------------------------------------------
# PRE: needs board
# POST: returns puzzle with slide right if possible
# PURPOSE: slides a puzzle piece right by one block
def moveRight(board):
    emptyIndex = board.index("0")  # find empty block
    if emptyIndex % 3 == 0:
        board = [9] * 9  # fills with invalid numbers to allow it to be flagged later
        return board
    else:
        swapIndex = emptyIndex - 1
    # Slide
    temp = board[swapIndex]
    board[swapIndex] = board[emptyIndex]
    board[emptyIndex] = temp
    return board


# ------------------------------------------------------------------------
# PRE: needs board
# POST: prints board
# PURPOSE: displays board in a nicely 3x3 format
def PrintBoard(board):
    for i in range(PUZZLE_SIZE):
        if i % ROW_SIZE == 0:
            if board[i] == "0":
                print("_ " + board[i + 1] + " " + board[i + 2])
            elif board[i + 1] == "0":
                print(board[i] + " _ " + board[i + 2])
            elif board[i + 2] == "0":
                print(board[i] + " " + board[i + 1] + " _")
            else:
                print(board[i] + " " + board[i + 1] + " " + board[i + 2])
    print()


# ------------------------------------------------------------------------
# PRE: needs four values
# POST: returns the order of largest -> smallest of the 4
# PURPOSE: basically sort 4 values from largest to the smallest
def FindValueRanks(val, val2, val3, val4):
    valueList = [val, val2, val3, val4]
    largest = max(valueList)
    valueList.remove(largest)
    SecLargest = max(valueList)
    smallest = min(valueList)
    valueList.remove(smallest)
    SecSmallest = min(valueList)
    return largest, SecLargest, smallest, SecSmallest


# ------------------------------------------------------------------------
# PRE: needs a list
# POST: returns a string
# PURPOSE: convert lists to string
def ListsToString(sentence):
    sentence = list(sentence)
    newString = ""
    for word in sentence:
        newString += str(word)  # concatenate all strings together
    newString = newString.strip()  # strip whitespace
    return newString


# ------------------------------------------------------------------------
# PRE: needs two states
# POST: returns the solved puzzle
# PURPOSE: solves the sliding puzzle
def Solve_Puzzle(currentState, goalState):
    queueNum = Q_SIZE  # initialize queue size
    puzzleQueue = PriorityQueue()  # instantiate priority queue data structure
    strGoalState = ListsToString(goalState)  # conversion to string to later method
    puzzleQueue.put((queueNum, int(strGoalState)))
    queueNum -= 1
    dynamic = 0
    loops = 0
    # Print Original Board
    PrintBoard(currentState)
    # Preset Previous
    previousState = currentState
    strCurrentState = ListsToString(currentState)
    alreadyUsed = set()
    alreadyUsed.add(strCurrentState)
    while puzzleQueue.not_empty:  # A failsafe atleast in this program
        print("-------------------------------------------------------------------------------------")
        print("Dynamic Range =" + str(dynamic))
        print("Steps =" + str(loops))

        # Copy board 4 times
        UpBoard = copy.deepcopy(currentState)
        DownBoard = copy.deepcopy(currentState)
        LeftBoard = copy.deepcopy(currentState)
        RightBoard = copy.deepcopy(currentState)

        # Do the 4 moves
        UpBoard = moveUp(UpBoard)
        DownBoard = moveDown(DownBoard)
        LeftBoard = moveLeft(LeftBoard)
        RightBoard = moveRight(RightBoard)

        # Calculate Manhattan Distance for all 4
        # as long as the board is valid
        if 9 not in UpBoard:    # flagged from earlier
            ManHatUp = Manhattan_Distance_Function(UpBoard, goalState)  # find distance of up board
        else:
            ManHatUp = 100  # flag
        if 9 not in LeftBoard:   # flagged from earlier
            ManHatLeft = Manhattan_Distance_Function(LeftBoard, goalState)  # find distance of left board
        else:
            ManHatLeft = 101  # flag
        if 9 not in DownBoard:   # flagged from earlier
            ManHatDown = Manhattan_Distance_Function(DownBoard, goalState)  # find distance of down board
        else:
            ManHatDown = 102  #flag
        if 9 not in RightBoard:  # flagged from earlier
            ManHatRight = Manhattan_Distance_Function(RightBoard, goalState)  # find distance of right board
        else:
            ManHatRight = 103  #flag

        # Rank the values
        largest, SecLargest, smallest, SecSmallest = FindValueRanks(ManHatUp, ManHatLeft, ManHatDown, ManHatRight)
        print("Previous Board Distance: " + str(Manhattan_Distance_Function(currentState, goalState)))

        # convert lists to strings so they can be stored in a tuple within the priority queue
        UpBoard = ListsToString(UpBoard)
        DownBoard = ListsToString(DownBoard)
        LeftBoard = ListsToString(LeftBoard)
        RightBoard = ListsToString(RightBoard)
        # Testing Only
        '''print(UpBoard)
        print(DownBoard)
        print(LeftBoard)
        print(RightBoard)'''

        if loops < Q_SIZE: # soooo this is basically an arbitrary number to keep the program from running infinitely
            # *****************This needs to be improved***************
            if smallest == ManHatUp and SecSmallest == ManHatDown and SecLargest == ManHatLeft and largest == ManHatRight:  # U D L R  #-1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
            elif smallest == ManHatUp and SecSmallest == ManHatDown and SecLargest == ManHatRight and largest == ManHatLeft:  # U D R L #2
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
            elif smallest == ManHatUp and SecSmallest == ManHatLeft and SecLargest == ManHatDown and largest == ManHatRight:  # U L D R #3
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
            elif smallest == ManHatUp and SecSmallest == ManHatLeft and SecLargest == ManHatRight and largest == ManHatDown:  # U L R D #4
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
            elif smallest == ManHatUp and SecSmallest == ManHatRight and SecLargest == ManHatLeft and largest == ManHatDown:  # U R L D #5
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
            elif smallest == ManHatUp and SecSmallest == ManHatRight and SecLargest == ManHatDown and largest == ManHatLeft:  # U R D L #6
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
            elif smallest == ManHatDown and SecSmallest == ManHatUp and SecLargest == ManHatLeft and largest == ManHatRight:  # D U L R #7
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
            elif smallest == ManHatDown and SecSmallest == ManHatUp and SecLargest == ManHatRight and largest == ManHatLeft:  # D U R L #8
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
            elif smallest == ManHatDown and SecSmallest == ManHatLeft and SecLargest == ManHatRight and largest == ManHatUp:  # D L R U #9
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
            elif smallest == ManHatDown and SecSmallest == ManHatLeft and SecLargest == ManHatUp and largest == ManHatRight:  # D L U R #-10
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
            elif smallest == ManHatDown and SecSmallest == ManHatRight and SecLargest == ManHatLeft and largest == ManHatUp:  # D R L U #-1-1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
            elif smallest == ManHatDown and SecSmallest == ManHatRight and SecLargest == ManHatUp and largest == ManHatLeft:  # D R U L #-12
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
            elif smallest == ManHatLeft and SecSmallest == ManHatUp and SecLargest == ManHatDown and largest == ManHatRight:  # L U D R #-13 -13
                print("LeftBoard = Smallest " + str(ManHatLeft))
                print("UpBoard =  SecSmallest" + str(ManHatUp))
                print("DownBoard = SecLargest" + str(ManHatDown))
                print("RightBoard = Largest" + str(ManHatRight))
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
            elif smallest == ManHatLeft and SecSmallest == ManHatUp and SecLargest == ManHatRight and largest == ManHatDown:  # L U R D #-14
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
            elif smallest == ManHatLeft and SecSmallest == ManHatDown and SecLargest == ManHatUp and largest == ManHatRight:  # L D U R #-15
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
            elif smallest == ManHatLeft and SecSmallest == ManHatDown and SecLargest == ManHatRight and largest == ManHatUp:  # L D R U #-16
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
            elif smallest == ManHatLeft and SecSmallest == ManHatRight and SecLargest == ManHatUp and largest == ManHatDown:  # L R U D #-17
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
            elif smallest == ManHatLeft and SecSmallest == ManHatRight and SecLargest == ManHatDown and largest == ManHatUp:  # L R D U #-18
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
            elif smallest == ManHatRight and SecSmallest == ManHatUp and SecLargest == ManHatDown and largest == ManHatLeft:  # R U D L #-19
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
            elif smallest == ManHatRight and SecSmallest == ManHatUp and SecLargest == ManHatLeft and largest == ManHatDown:  # R U L D #20
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
            elif smallest == ManHatRight and SecSmallest == ManHatLeft and SecLargest == ManHatUp and largest == ManHatDown:  # R L U D #21-1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
            elif smallest == ManHatRight and SecSmallest == ManHatLeft and SecLargest == ManHatDown and largest == ManHatUp:  # R L D U #22
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
            elif smallest == ManHatRight and SecSmallest == ManHatDown and SecLargest == ManHatLeft and largest == ManHatUp:  # R D L U #23
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1
            elif smallest == ManHatRight and SecSmallest == ManHatDown and SecLargest == ManHatUp and largest == ManHatLeft:  # R D U L #24
                if ManHatLeft < 99:
                    puzzleQueue.put((queueNum, LeftBoard))
                    queueNum += -1
                if ManHatUp < 99:
                    puzzleQueue.put((queueNum, UpBoard))
                    queueNum += -1
                if ManHatDown < 99:
                    puzzleQueue.put((queueNum, DownBoard))
                    queueNum += -1
                if ManHatRight < 99:
                    puzzleQueue.put((queueNum, RightBoard))
                    queueNum += -1

        #  FAILSAFE for if program checks fail
        elif loops > 100:  # if its starts going infinite (which shouldn't happen)
            # randomly start jumping to different loop numbers as to clear the queue and keep trying until its solved (brute force)
            loops -= random.randint(1, Q_SIZE)

        # Go to next puzzle slide
        nextState = str(puzzleQueue.get()[1])
        nextState = list(nextState)
        if nextState == previousState:  # if its the same as previous state, don't do it
            nextState = str(puzzleQueue.get()[1]) # get the next next one
            nextState = list(nextState)
        else:
            nextState = ListsToString(nextState)
            while nextState in alreadyUsed and puzzleQueue.not_empty:  # same as one already used
                nextState = str(puzzleQueue.get()[1])  # get the next next one
            alreadyUsed.add(nextState)
            nextState = list(nextState)
        if smallest == 0:  # if its 0 it means its solved
            nextState = list(nextState)
            PrintBoard(nextState) # HURRAY!
            print("FINISHED")
            return  #  I know this is no bueno and again patheic coding my apoglizes
        else:  # if not done
            print(" STEP")
            nextState = list(nextState)
            PrintBoard(currentState)  # print board
            # copies
            previousState = copy.deepcopy(currentState)
            currentState = copy.deepcopy(nextState)

        # Number of Steps
        loops += 1
        dynamic += 1 # Only used in the case, where all failsafes failed and it had to adjust to randomize (brute force) to complete

# ------------------------------------------------------------------------
# driver code
def main():
    goalState = ['1', '2', '3', '4', '5', '6', '7', '8', '0']  # set the goal state
    string = input("Please Enter Current State: ")  # ask for current state
    string = INPUT8
    if not ValidInput(string):  # check if current state is valid
        print('incorrect input')
    else:
        print("Correct Input")
        currentState = (list(string))  # otherwise create current state
        print(currentState)
        if isPossible(currentState):  # check if solvable?
            print("Possible!")
            Solve_Puzzle(currentState, goalState)
        else:
            print("Not Possible!")



main()
