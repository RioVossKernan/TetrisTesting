//MANUALLY SET THESE VALUES
const grid_width = 6;
const grid_height = 6;

//UPDATE SCREEN
function draw_screen(stg, inst_num){
    draw_next_button(stg, inst_num);
    drawStateIndicator(stg, inst_num)
    drawGrid(stg, inst_num)
    stg.render(svg, document)
}

//NEXT BUTTON
function draw_next_button(stg, inst_num){
    let next_button = new TextBox({
        text: "CLICK HERE",
        coords: {x: 100, y:10},
        color: 'Black',
        height: 30,
        width: 120,

        events: [
            {event: 'click', callback: () => {
                inst_num++;
                if (inst_num >= instances.length) {
                    inst_num = 0;
                }
                //make a new stage to draw the new state
                stg = new Stage();
                draw_screen(stg, inst_num)
            }}
        ]
    }); 
    stg.add(next_button);
}

//STATE INDICATOR TEXT BOX
function drawStateIndicator(stg, inst_num){
    let state_indicator = new TextBox({
        text: `STATE NUM = ${inst_num}`,
        coords: {x: 300, y:10},
        color: 'Black',
        height: 30,
        width: 120,
    }); 
    stg.add(state_indicator);
}

function drawGrid(stg, inst_num) {
    //INITIALIZE GRID
    let tetrisGrid = new Grid({
        grid_location: {x: 50, y:50},
        cell_size: {x_size: 40, y_size: 40},
        grid_dimensions: {x_size: grid_width, y_size: grid_height}
    })

    //ADD VALUES TO GRID
    for (r = 0; r < grid_height; r++) {
        for (c = 0; c < grid_width; c++) {
            let tiles = instances[inst_num].signature('Board').join(instances[inst_num].field('tiles')).toString()
            if (tiles.includes(`${c}, ${r}`)){
                tetrisGrid.add({x: c, y: grid_height - r - 1}, new Rectangle({height: 40, width: 40, color: "green", borderColor: "black"}));
            }
        }
    }
    stg.add(tetrisGrid);
}

draw_screen(new Stage(), 0);