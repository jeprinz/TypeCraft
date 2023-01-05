import React from 'react'
import './App.css'
import { editor } from './zypr-generic/editor/EditorA1'
import './zypr-generic/frontend/Frontend1.css'

type Props = {}

type State = {}

export default class App extends React.Component<Props, State> {
  state = {}
  constructor(props: Props) {
    super(props)
  }

  render() {
    return (
      <div className="app">
        {editor}
      </div>
    )
  }
}
